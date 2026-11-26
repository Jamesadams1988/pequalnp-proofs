"""Check the literal graph and enumerate minimal center choices by left complement."""
from itertools import combinations
from pathlib import Path
import json
import re
import sys

root = Path(__file__).resolve().parent
rows = json.loads((root / "rows.json").read_text())
n = len(rows)
full = (1 << n) - 1
assert n == 21 and all(0 < row <= full for row in rows)
edges = {(p, n + l) for p, row in enumerate(rows) for l in range(n) if row >> l & 1}
if len(sys.argv) > 1:
    statement = json.loads(Path(sys.argv[1]).read_text())["statement"]
    desk_edges = [tuple(map(int, e)) for e in re.findall(r"\(x (\d+) && x (\d+)\)", statement)]
    assert len(desk_edges) == len(edges) and set(desk_edges) == edges
assert len(edges) == 104
assert all((a & b).bit_count() <= 1 for a, b in combinations(rows, 2))
# Shifted diagonal gives one edge in each row and column, including row zero.
matching = [(p, n + (p + 5) % n) for p in range(n)]
assert len({b for _, b in matching}) == n and set(matching) <= edges

# Enumerate omitted left vertices. Every neighbor of an omitted point is a forced
# right center. This unique smallest completion for the chosen left side suffices.
histogram = {}
ordinary_min = 2*n
ordinary_achievers = []
mixed_min = 2*n
mixed_achievers = []
def visit(p, omitted, neighbors):
    global ordinary_min, ordinary_achievers, mixed_min, mixed_achievers
    if p < n:
        visit(p+1, omitted, neighbors)
        visit(p+1, omitted | 1<<p, neighbors | rows[p])
        return
    size = n - omitted.bit_count() + neighbors.bit_count()
    if size < ordinary_min:
        ordinary_min, ordinary_achievers = size, []
    if size == ordinary_min:
        ordinary_achievers.append((omitted, neighbors))
    if omitted not in (0, full) and neighbors not in (0, full):
        if size < mixed_min:
            mixed_min, mixed_achievers = size, []
        if size == mixed_min:
            mixed_achievers.append((omitted, neighbors))
        a = omitted.bit_count()
        histogram[a] = min(histogram.get(a, 2*n), size)

visit(0, 0, 0)
print("edges",len(edges),"matching",len(matching),"C4-free",True)
print("minimum centers",ordinary_min,"achievers",len(ordinary_achievers))
print("proper mixed minimum",mixed_min,"achievers",len(mixed_achievers))
print("mixed min by omitted left count",sorted(histogram.items()))
print("mixed minimizing pairs (omitted left, forced right masks)",mixed_achievers)
assert ordinary_min == 21 and set(ordinary_achievers) == {(0, 0), (full, full)}
for omitted, forced in mixed_achievers:
    # Removing any selected center must expose an edge with exactly that center.
    center = {p for p in range(n) if not (omitted >> p & 1)}
    center |= {n + l for l in range(n) if forced >> l & 1}
    assert all(any({a, b} & center == {v} for a, b in edges) for v in center)
assert mixed_min == 24 and len(mixed_achievers) == 2
print("total gate lower bound",len(edges)+ordinary_min-1)
print("proper mixed gate lower bound",len(edges)+mixed_min-1)
special_line = n
transferred = set(sorted((a,b) for a,b in edges if b == special_line)[:2])
stars = [set((a,b) for a,b in edges - transferred if a == p) for p in range(n)] + [transferred]
assert len(stars) == 22 and all(len(group) >= 2 for group in stars)
assert set.union(*stars) == edges and sum(map(len, stars)) == len(edges)
print("full point shore plus one line center",len(edges) + len(stars) - 1)

# Small implementation control for erasing negative literals from safe products.
# This path has edges 0--2, 0--3, 1--2. A truth table occupies one 16-bit word.
tiny_edges = [(0,2),(0,3),(1,2)]
f = sum(1 << x for x in range(16) if any((x >> a) & (x >> b) & 1 for a,b in tiny_edges))
pos = [sum(1 << x for x in range(16) if (x >> i) & 1) for i in range(4)]
lits = pos + [0xffff ^ x for x in pos]
clause = [0] * 256
for mask in range(1, 256):
    low = mask & -mask
    clause[mask] = clause[mask ^ low] | lits[low.bit_length()-1]
safe = 0
for a in range(256):
    for b in range(256):
        output = clause[a] & clause[b]
        if not output & ~f:
            assert output == clause[a & 15] & clause[b & 15]
            safe += 1
print("signed-clause pairs checked on the four-vertex control",256**2,"safe",safe)
