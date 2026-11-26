"""Check each transitive upstream project import against the research pin."""
from pathlib import Path
import json
import re
import subprocess
import sys

pin = 'c468e9f20b8fea4dc13ef9abde683cb439979a1c'
mathlib = 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
project = Path(sys.argv[1]).resolve()
root = Path(subprocess.check_output(['git', '-C', project, 'rev-parse', '--show-toplevel'], text=True).strip())
assert (project/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.36.0'
manifest = json.loads((project/'lake-manifest.json').read_bytes())
assert next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib') == mathlib
assert subprocess.check_output(['git','-C',project/'.lake/packages/mathlib','rev-parse','HEAD'], text=True).strip() == mathlib

def imports(src):
    return set(re.findall(r'^\s*(?:public\s+|meta\s+)*import\s+(PEqualNP[\w.]*)\s*$', src, re.M))

pending = set()
for file in Path(__file__).resolve().parent.rglob('*.lean'):
    if file.name not in {'From8455.lean','From8459.lean'}:
        pending.update(imports(file.read_text()))
seen = set()
while pending:
    module = pending.pop()
    if module in seen:
        continue
    path = Path(*module.split('.')).with_suffix('.lean')
    data = (project/path).read_bytes()
    upstream = subprocess.check_output(['git','-C',root,'show',pin+':lean/'+str(path)])
    assert data == upstream, module
    seen.add(module)
    pending.update(imports(data.decode()) - seen)
print(f"Verified {len(seen)} transitive upstream project modules and the Lean and Mathlib pins.")

# The expensive upstream donor has an explicit, optional kernel build.
import hashlib
donor = subprocess.check_output(['git','-C',root,'show',pin+':lean/PEqualNP/Outside/L_meta_8455.lean'])
assert hashlib.sha256(donor).hexdigest() == '5e1617080cd587375490e805dd8f0d8eb0b02cc5f9cb065ff356ca0601bbda98'
print('Upstream L-meta-8455 donor source matches its pinned SHA-256.')

second = subprocess.check_output(['git','-C',root,'show',pin+':lean/PEqualNP/Outside/L_meta_8459.lean'])
assert hashlib.sha256(second).hexdigest() == 'be5601110708f4ffb2f98e0a3040262d62e89639d6783b493b47f2e08c38bc4f'
print('Upstream L-meta-8459 donor source matches its pinned SHA-256.')
