"""Enumerate ownership of each edge and build full-basis first-wire witnesses."""
import itertools
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
assignment = json.loads((here / 'statement.json').read_text())
edges = [tuple(map(int, e)) for e in re.findall(r'x (\d+) && x (\d+)', assignment['statement'])]
assert len(set(edges)) == len(edges) == 12 and all(0 <= u < v < 9 for u, v in edges)
neighbors = [{b if a == i else a for a, b in edges if i == a or i == b} for i in range(9)]
assert max(len(a & b) for a, b in itertools.combinations(neighbors, 2)) == 1
orientations = []
for ownership in itertools.product(range(2), repeat=len(edges)):
    stars = {}
    for (u, v), side in zip(edges, ownership):
        center, leaf = (u, v) if side == 0 else (v, u)
        stars.setdefault(center, []).append(leaf)
    orientations.append(stars)
minimum = min(map(len, orientations))
optimal = [s for s in orientations if len(s) == minimum]
covers = sorted({tuple(sorted(s)) for s in optimal})
options = [('not', 5, 5)] + [(op, 5, j) for op in ('and', 'or') for j in (6, 7, 8)]

def matching_center(stars, op, a, b):
    for c, leaves in stars.items():
        if op == 'or' and a in leaves and b in leaves:
            return c
        if op == 'and' and len(leaves) == 1 and {a,b} == {c,leaves[0]}:
            return c
    return None

def construct(stars, first, center):
    op,a,b=first
    gates=[[op,a] if op=='not' else [op,a,b]]
    def gate(operator,u,v):
        gates.append([operator,u,v])
        return 9+len(gates)-1
    outputs=[]
    for c, leaves in sorted(stars.items()):
        if c == center and op=='and':
            outputs.append(9)
            continue
        if c == center and op=='or':
            wires=[9]+[v for v in leaves if v not in (a,b)]
        else:
            wires=list(leaves)
        acc=wires[0]
        for v in wires[1:]:
            acc=gate('or',acc,v)
        outputs.append(gate('and',c,acc))
    acc=outputs[0]
    for w in outputs[1:]:
        acc=gate('or',acc,w)
    return {'gates':gates,'output':acc}

def simulate(circuit, assignment):
    wires=[bool(assignment >> j & 1) for j in range(9)]
    for op,*args in circuit['gates']:
        assert all(0<=j<len(wires) for j in args)
        val=[wires[j] for j in args]
        output = (not val[0]) if op=='not' else (all(val) if op=='and' else any(val))
        wires.append(output)
    return wires[circuit['output']]

witnesses={}
print('edge count',len(edges),'minimum centers',minimum,'minimum covers',covers)
print('edge partitions into five nonempty stars',len(optimal))
for option in options:
    available=[(s,matching_center(s,*option)) for s in optimal]
    usable=[(s,c) for s,c in available if c is not None]
    stars, designated = usable[0] if usable else (optimal[0],None)
    c=construct(stars,option,designated)
    for x in range(512):
        assert simulate(c,x) == any(x >> u & 1 and x >> v & 1 for u,v in edges)
    name = option[0] + str(option[1]) + ('' if option[0]=='not' else '_' + str(option[2]))
    witnesses[name]=c
    print(name,'optimal orientations using the first gate',len(usable),'gates',len(c['gates']))
if __name__=='__main__':
    import sys
    if sys.argv[1:]==['--write']:
        (here/'witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')
    else:
        assert json.loads((here/'witnesses.json').read_text())==witnesses
