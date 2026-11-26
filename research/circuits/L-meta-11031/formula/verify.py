"""Replay all first-gate minima and check matching constructions."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
edges = [(0,4), (1,5), (0,6), (1,6), (2,6), (0,7), (3,7), (4,7), (2,8), (3,8), (5,8), (7,8)]
tokens = [('raw', 0, 0)] + [('not', i, i) for i in range(9)]
tokens += [(op, i, j) for op in ('and', 'or') for i, j in combinations(range(9), 2)]
records = [tuple(line.split()) for line in (root/'first-results.txt').read_text().splitlines()]
expected = {(op, int(a), int(b)): int(k) for op,a,b,k in records}
assert len(expected) == len(records) == len(tokens) and set(expected) == set(tokens)
if len(sys.argv) == 2:
    binary = str(Path(sys.argv[1]).resolve())
    for op, a, b in tokens:
        line = subprocess.check_output([binary, op, str(a), str(b)], text=True).split()
        assert line == [op, str(a), str(b), str(expected[op,a,b])]

# A five-star partition uses 12 binary gates for the stars and four final OR gates.
ordinary = set()
for mask in range(1 << len(edges)):
    stars = {}
    for k, (a, b) in enumerate(edges):
        if mask >> k & 1:
            a,b = b,a
        stars.setdefault(a, []).append(b)
    if len(stars) == 5:
        for center, leaves in stars.items():
            if len(leaves) == 1:
                ordinary.add(('and', *sorted([center, leaves[0]])))
            ordinary.update(('or', a, b) for a,b in combinations(sorted(leaves), 2))

# A 16-gate formula with x7 OR x8 built first. Each intermediate has fanout one.
def special(x):
    u = [bool(x >> i & 1) for i in range(9)]
    first = u[7] or u[8]
    return ((u[2] and u[6]) or (u[1] and (u[5] or u[6]))
            or (u[0] and (u[4] or u[6]))
            or (first and (u[3] or ((u[2] or u[5] or u[7]) and (u[0] or u[4] or u[8])))))

def target(x):
    return any((x >> a & 1) and (x >> b & 1) for a,b in edges)

assert sum(not target(x) for x in range(512)) == 60
assert all(special(x) == target(x) for x in range(512))
assert ('or', 7, 8) not in ordinary
ordinary.add(('or', 7, 8))
assert ordinary == {case for case in tokens if expected[case] == 16}
assert expected['raw', 0, 0] == 17 and all(n in (16,17) for n in expected.values())
print('raw minimum: 17 leaves, 16 gates')
for op in ('not', 'and', 'or'):
    counts = Counter(v for (kind, _, _), v in expected.items() if kind == op)
    print(f'{op}: 16 gates in {counts[16]} cases, 17 gates in {counts[17]} cases')
print('25 optimal first gates occur in five-star partitions; the remaining x7 OR x8 formula passes all 512 inputs.')
