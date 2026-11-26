"""Check each transitive upstream project import against the research pin."""
from pathlib import Path
import json
import re
import subprocess
import sys

pin = 'e6a99b96b6c8eea0ce4874719a57f7817595a4b2'
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
