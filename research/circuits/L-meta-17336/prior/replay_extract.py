"""Extract only executable Boolean assertions from grigorescu's PR #22380."""
import csv
import hashlib
import re
from pathlib import Path

p=Path(__file__).resolve().parent
source_bytes = (p / 'Prior17335.lean').read_bytes()
def digest(data):
    return hashlib.sha256(data).hexdigest()
if digest(source_bytes) != '4defc64e8c1808d31eb16e4d092560256cadea0b1f32be2d604d9413002b10a2':
    raise ValueError('unexpected source digest')
source = source_bytes.decode()
defs={}
checks=[]
for block in re.split(r'\n(?=\S)', source):
    m=re.match(r'(?:noncomputable )?(?:def|abbrev) ([\w\']+)\b',block)
    if m:
        defs[m[1]]=block
    m=re.match(r'(?:lemma|theorem) (\w+) : (.*?) := by decide \+kernel$',block.strip(),re.S)
    if m:
        checks.append((m[1],m[2][:-7] if m[2].endswith(' = true') else 'decide (' + m[2] + ')'))

def names(s):
    return set(re.findall(r"\b[\w']+\b",s)) & defs.keys()

selected=set()
queue=list(names(' '.join(x[1] for x in checks)))
while queue:
    key=queue.pop()
    if key in selected:continue
    selected.add(key)
    queue.extend(names(defs[key]))

# Admit only fixed, reviewed numerical declarations and test expressions.
allow_bytes = (p / 'allowlist.tsv').read_bytes()
if digest(allow_bytes) != 'd67441b8ad9c81be8e4ff88d61d3d8c3c1ce39d3d46f7f2f6856a53661ba8f89':
    raise ValueError('unexpected replay allowlist')
allowed = [tuple(row) for row in csv.reader(allow_bytes.decode().splitlines(), delimiter='\t')][1:]
found = [('definition', key, digest(text.encode())) for key, text in defs.items() if key in selected]
found.extend(('assertion', key, digest(text.encode())) for key, text in checks)
if found != allowed or len(selected) != 208 or len(checks) != 135:
    raise ValueError('replay declarations or checks differ from the reviewed list')

def translate(s):
    if s.startswith('def st '):return "def st (n : Nat) (f : Nat → Bool) : Bool := f n"
    if s.startswith('def prd '):return "def prd (t : Nat) (h : Nat → Bool) : Bool := if t=0 then false else h (t-1)"
    if s.startswith('def pos '):return "def pos (t : Nat) : Bool := decide (0 < t)"
    s=s.removeprefix('noncomputable ')
    for op,rep in [('Bool.rec','bRec'),('Nat.rec','nRec'),('List.rec','lRec'),('Prod.rec','pRec')]:
        needle=op+' (motive := fun _ => '
        while needle in s:
            at=s.index(needle)
            i=at+len(needle)
            j=i;depth=1
            while depth:
                depth += (s[j]=='(') - (s[j]==')')
                j+=1
            s=s[:at]+rep+' (β := '+s[i:j-1]+')'+s[j:]
    return s
intro="""import Std

local notation "ℕ" => Nat

namespace PriorReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[macro_inline] def bRec {β : Sort u} (e t : β) (b : Bool) : β :=
  bif b then t else e
@[macro_inline] def pRec {α β₁ β : Type} (f : α → β₁ → β) (p : α × β₁) : β :=
  f p.1 p.2
@[specialize] def nRec {β : Type u} (z : β) (s : Nat → β → β) : Nat → β
  | 0 => z
  | n+1 => s n (nRec z s n)
@[specialize] def lRec {α : Type v} {β : Type u} (z : β) (s : α → List α → β → β) : List α → β
  | [] => z
  | x :: xs => s x xs (lRec z s xs)

"""
body='\n\n'.join(translate(v.strip()) for k,v in defs.items() if k in selected)
# A separate thunk for each check exposes per-assertion timings.
tail='\n'.join('def check_'+n+' (_ : Unit) : Bool := '+expr for n,expr in checks)
tail+='\n\ndef checks : List (String × (Unit → Bool)) := [\n'+',\n'.join('  ("'+n+'", check_'+n+')' for n,_ in checks)+']\nend PriorReplay\n'
tail+='''
def main (args : List String) : IO Unit := do
  for (name, test) in PriorReplay.checks do
    if args.isEmpty || args.any (fun pre => name.startsWith pre) then
      let start ← IO.monoMsNow
      unless test () do throw (IO.userError name)
      IO.println s!"{name} true {(← IO.monoMsNow) - start}ms"
      (← IO.getStdout).flush
'''
generated = intro + body + '\n\n' + tail
if digest(generated.encode()) != '299122354221e2fa0bcda58667c661d3dfd1c0f0f47d461b6f518bf2f864088e':
    raise ValueError('generated numerical program differs from reviewed program')
(p / 'Numerical.lean').write_text(generated)
print('executable definitions',len(selected),'explicit Boolean assertions',len(checks))
