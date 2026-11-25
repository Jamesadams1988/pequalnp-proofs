"""Build and replay the partial-truth read-once checker using only Python 3 and C++20."""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
TARGET=0xfe80fe00fe00e800
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--all',action='store_true',help='also run all 118 children of head 13')
parser.add_argument('--frontier',type=Path,help='validate rows.txt directly against this SignedFrontier.lean')
args=parser.parse_args()
rows=list(map(int,(HERE/'rows.txt').read_text().split()))
assert len(rows)==256 and set(rows)==set(range(64))
assert all(((TARGET>>r)&1)==(j>=128) for j,r in enumerate(rows))
frontier=args.frontier or next((p for p in (HERE.parent/'SignedFrontier.lean',HERE.parent/'search/SignedFrontier.lean') if p.is_file()),None)
if frontier is not None:
    line=frontier.read_text().split('def xs : List W := [',1)[1].split(']',1)[0]
    inputs=[int(w.strip(),16) for w in line.split(',')]
    assert len(inputs)==6 and rows==[sum((w>>j&1)<<i for i,w in enumerate(inputs)) for j in range(256)]
print('Verified 256 row positions and all 64 assignments.',flush=True)

def fields(line):
    return dict(field.split('=',1) for field in line.split())

with tempfile.TemporaryDirectory() as folder:
    for name in ['controls','profile']:
        subprocess.run(['g++','-std=c++20','-O3',str(HERE/(name+'.cpp')),'-o',f'{folder}/{name}'],check=True)
    subprocess.run([f'{folder}/controls'],check=True)
    for index in ([17,-1] if args.all else [17]):
        text=subprocess.check_output([f'{folder}/profile',str(HERE/'rows.txt'),str(index),'17','1'],text=True)
        records=[fields(l) for l in text.splitlines() if l.startswith('root=')]
        zero=fields(next(l for l in text.splitlines() if l.startswith('zero_distinct=')))
        assert all(r['hit']=='0' for r in records)
        assert len(records)==(118 if index==-1 else 1)
        assert sum(int(r['nodes']) for r in records)+(index==-1)==(10144859 if index==-1 else 65930)
        assert int(zero['zero_distinct'])==(434316 if index==-1 else 12053)
        print('head13' if index==-1 else 'child17',zero,flush=True)
        for l in text.splitlines():
            if l.startswith('partial_depth='): print(l,flush=True)
