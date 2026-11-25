"""Emit the exact residual catalogue and a Lean soundness proof."""
from final_hole import AX, ALL, S, ZERO, add, cuts, subsets
v={1<<i:{a} for i,a in enumerate(AX)}
for mask in range(1,ALL+1):
    bank=v.setdefault(mask,set())
    for a in subsets(mask):
        b=mask^a
        if a and a<b:
            bank.update(add(x,y) for x in v[a] for y in v[b])
    todo=list(bank)
    while todo:
        for y in cuts(todo.pop()):
            if y not in bank:
                bank.add(y);todo.append(y)
assert sum(map(len,v.values()))==246

def literal(x): return '⟨'+','.join(map(str,x))+'⟩'
print('''import Mathlib
namespace FinalHole
structure Line where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  rhs : ℤ
  deriving DecidableEq

def add (x y : Line) : Line := ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d,x.rhs+y.rhs⟩
def cut (x : Line) (k : ℕ) : Line := ⟨x.a/k,x.b/k,x.c/k,x.d/k,-((-x.rhs)/k)⟩
def divides (k : ℕ) (x : Line) : Prop :=
  (k:ℤ) ∣ x.a ∧ (k:ℤ) ∣ x.b ∧ (k:ℤ) ∣ x.c ∧ (k:ℤ) ∣ x.d
instance (k : ℕ) (x : Line) : Decidable (divides k x) := by unfold divides; infer_instance
abbrev Mask := BitVec 7

def ax : Fin 7 → Mask × Line := !['''+',\n'.join(f'({1<<i},{literal(x)})' for i,x in enumerate(AX))+']')
print('def bank (m : Mask) : List Line := match m.toNat with')
for mask in v:print(f'  | {mask} => ['+', '.join(literal(x) for x in sorted(v[mask]))+']')
print('  | _ => []')
print('''
def sumRaw (m : Mask) : Line := (List.finRange 7).foldl (fun acc i =>
  if m.getLsbD i.val then add acc (ax i).2 else acc) ⟨0,0,0,0,0⟩

inductive ReadOnce : Mask → Line → Prop
  | leaf (i : Fin 7) : ReadOnce (ax i).1 (ax i).2
  | join {m n x y} : ReadOnce m x → ReadOnce n y → m &&& n = 0 →
    ReadOnce (m ||| n) (add x y)
  | div {m x} (k : ℕ) : ReadOnce m x → 0 < k → divides k x → ReadOnce m (cut x k)

set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem leaves : ∀ i : Fin 7, (ax i).2 ∈ bank (ax i).1 := by decide +kernel

theorem joins : ∀ m n : Mask, m &&& n = 0 → ∀ x ∈ bank m, ∀ y ∈ bank n,
    add x y ∈ bank (m ||| n) := by decide +kernel

theorem divs : ∀ m : Mask, ∀ x ∈ bank m, ∀ k : Fin 4, 0 < k.val → divides k.val x →
    cut x k.val ∈ bank m := by decide +kernel

def small (a : ℤ) := a ≠ 0 ∧ a.natAbs ≤ 3
instance (a : ℤ) : Decidable (small a) := by unfold small; infer_instance

theorem magnitude : ∀ m : Mask, ∀ x ∈ bank m, x = ⟨0,0,0,0,0⟩ ∨
    small x.a ∨ small x.b ∨ small x.c ∨ small x.d := by decide +kernel

theorem inBank {m x} (h : ReadOnce m x) : x ∈ bank m := by
  induction h with
  | leaf i => exact leaves i
  | join _ _ dis ih jh => exact joins _ _ dis _ ih _ jh
  | @div m x k _ pos hdiv ih =>
    rcases magnitude m x ih with rfl | nz
    · simpa [cut] using ih
    have bound (a : ℤ) (small_a : small a) (dvd : (k:ℤ) ∣ a) : k ≤ 3 :=
      (Int.natAbs_le_of_dvd_ne_zero dvd small_a.1).trans small_a.2
    have hl : k ≤ 3 := by
      rcases hdiv with ⟨da,db,dc,dd⟩
      rcases nz with ha | hb | hc | hd
      · exact bound _ ha da
      · exact bound _ hb db
      · exact bound _ hc dc
      · exact bound _ hd dd
    exact divs m x ih ⟨k,by omega⟩ pos hdiv

theorem noFalseChecked : ∀ m : Mask, ∀ x ∈ bank m, x ≠ ⟨0,0,0,0,1⟩ := by decide +kernel

theorem noFalse {m x} (h : ReadOnce m x) : x ≠ ⟨0,0,0,0,1⟩ := noFalseChecked m x (inBank h)

theorem noDoubleChecked : ∀ m : Mask, ∀ x ∈ bank m,
    add (add x x) (sumRaw (~~~m)) ≠ ⟨0,0,0,0,1⟩ := by decide +kernel

theorem noDouble {m x} (h : ReadOnce m x) :
    add (add x x) (sumRaw (~~~m)) ≠ ⟨0,0,0,0,1⟩ := noDoubleChecked m x (inBank h)
end FinalHole
#print axioms FinalHole.noFalse
#print axioms FinalHole.noDouble''')
