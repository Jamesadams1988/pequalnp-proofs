"""Check the finite data in the star-circuit theorem for James Adams's row L-meta-9742."""
import itertools
import re
import sys
from collections import Counter
from pathlib import Path

# Row zero is the only deficient left vertex. Each listed value is a line label.
rows = [
    (17,23,25), (13,14,18,24), (14,15,19,25), (13,15,16,20),
    (14,16,17,21), (15,17,18,22), (16,18,19,23), (17,19,20,24),
    (18,20,21,25), (13,19,21,22), (14,20,22,23), (15,21,23,24),
    (16,22,24,25)
]
edges = [(p, l) for p, row in enumerate(rows) for l in row]
if len(sys.argv) > 1:
    import json
    statement = json.loads(Path(sys.argv[1]).read_text())["statement"]
    assert edges == [tuple(map(int, ab)) for ab in re.findall(r'\((\d+), (\d+)\)', statement)]
adj = [set() for _ in range(26)]
for p, l in edges:
    adj[p].add(l)
    adj[l].add(p)
left = frozenset(range(13))
right = frozenset(range(13,26))
assert len(edges) == 51 and min(map(len,adj)) == 3 and max(map(len,adj)) == 4
assert all(len(adj[a] & adj[b]) <= 1 for a,b in itertools.combinations(range(26),2))
minimal = Counter()
smallest = []
for mask in range(1<<13):
    pts = {p for p in left if mask >> p & 1}
    lns = set().union(*(adj[p] for p in left-pts))
    c = pts | lns
    # With points fixed, every one of these lines is forced. Test point minimality.
    if all(adj[p]-lns for p in pts):
        minimal[len(c)] += 1
        if len(c) <= 15:
            smallest.append(frozenset(c))
assert set(c for c in smallest if len(c) == 13) == {left,right}
assert sorted(minimal.items()) == [(13,2),(15,2),(16,24),(17,18),(18,210),(19,396),(20,34)]
mixed = [sorted(c) for c in smallest if len(c) == 15]
assert len(mixed) == 2
print('minimal covers by cardinality:', sorted(minimal.items()))
print('smallest covers omitting at least one center on each shore:', mixed)
allowed = {(u,v) for u,v in itertools.permutations(range(26),2) if adj[u] & adj[v]}
assert len(allowed) == 300
print('first gate attaining 63 in the restricted model: 300 ordered binary ORs')
print('other native first gates attaining 64: ',2*(1+26+26**2)-len(allowed))
print('minimum size 63; minimum depth 7; minimum with a center omitted on each shore 65')

from math import prod
forms = 2 * 3 * 15**12 * prod(range(1,24,2))
assert forms == 246181331996538903808593750
assert all(((104+8*r-1).bit_length()==7) == (r<=3) for r in range(13))
print('optimal labeled circuit bracketings:', forms)
