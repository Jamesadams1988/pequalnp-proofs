from itertools import combinations
from collections import Counter
from pathlib import Path
import subprocess, sys

base = Path(__file__).resolve().parent
edges = [(0,4),(0,5),(1,5),(2,6),(3,6),(0,7),(2,7),(4,7),(1,8),(3,8),(4,8),(6,8)]
cases = [('raw',0,0)] + [('not',i,i) for i in range(9)]
cases += [(op,a,b) for op in ('and','or') for a,b in combinations(range(9),2)]
rows = (base/'first-results.txt').read_text().splitlines()
assert len(rows)==len(cases)
opt = set()
counts = Counter()
for case, row in zip(cases, rows):
    op,a,b = case
    expected, i,j,n = row.split()
    assert (expected,int(i),int(j)) == case and int(n) in (16,17)
    if len(sys.argv)>1:
        assert subprocess.check_output([str(Path(sys.argv[1]).resolve()),op,i,j],text=True).strip()==row
    if n=='16': opt.add(case)
    counts[op,n]+=1

star = set()
for orient in range(4096):
    centers = {}
    for k,(a,b) in enumerate(edges):
        if orient>>k&1: a,b=b,a
        centers.setdefault(a,[]).append(b)
    if len(centers)!=5: continue
    for c,leaves in centers.items():
        if len(leaves)==1: star.add(('and',*sorted((c,leaves[0]))))
        star.update(('or',a,b) for a,b in combinations(sorted(leaves),2))
assert opt - star == {('or',6,8)} and not star - opt
assert len(star)==22

def parse(it):
    op=next(it)
    if op.isdigit(): return lambda v:v[int(op)]
    a=parse(it)
    if op=='!': return lambda v:not a(v)
    b=parse(it)
    return (lambda v:a(v) and b(v)) if op=='&' else (lambda v:a(v) or b(v))

def errors(text):
    it=iter(text)
    f=parse(it)
    assert not list(it)
    result=set()
    for x in range(512):
        v=[bool(x>>i&1) for i in range(9)]
        v.append(v[6] or v[8])
        if f(v)!=any(v[a] and v[b] for a,b in edges): result.add(x)
    return result

special='|&15|&7|42|&0|4|75&9|3&|28|1|46'
assert sum(c in '&|' for c in special)==15 and special.count('9')==1 and not errors(special)
signed='|&18|&5|10&!|51|3|4|67'
bad=errors(signed)
pos={1<<a|1<<b for a,b in edges}
neg={x for x in range(512) if not any(x&e==e for e in pos)}
maxneg={x for x in neg if not any(x|y==y and x!=y for y in neg)}
assert len(neg)==57 and len(maxneg)==13
assert sum(c in '&|!' for c in signed)==11 and len(bad)==109 and not bad & (pos|maxneg|{0,511})
print(sorted(counts.items()))
print('22 star-optimal first wires and one extra OR validated. The signed control fails 109 full assignments.')
