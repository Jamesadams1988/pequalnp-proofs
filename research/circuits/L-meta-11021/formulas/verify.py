"""Compare all 4096 formula minima against a separate vertex-cover computation."""
from collections import Counter
from pathlib import Path
import subprocess
import sys

EDGES = [(0, 4), (0, 5), (1, 5), (2, 6), (3, 6), (0, 7), (2, 7), (4, 7),
         (1, 8), (3, 8), (4, 8), (6, 8)]
FULL = (1 << len(EDGES)) - 1
records = subprocess.check_output([str(Path(sys.argv[1]).resolve())], text=True)
rows = [tuple(map(int, line.split())) for line in records.splitlines()]
assert len(rows) == FULL + 1 and [r[0] for r in rows] == list(range(FULL + 1))

covered = [sum(int(bool(v & (1 << i | 1 << j))) << n for n, (i, j) in enumerate(EDGES))
           for v in range(1 << 9)]
tau = [min(v.bit_count() for v, cover in enumerate(covered) if required & ~cover == 0)
       for required in range(FULL + 1)]
counts = Counter()
for mask, leaves, total in rows:
    assert leaves == mask.bit_count() + tau[mask]
    assert total == 11 + mask.bit_count() + tau[FULL ^ mask]
    counts[total] += 1
print("All 4096 residual leaf counts equal |R| + vertex-cover number of R.")
print("All 4096 compulsory-prefix minima equal 11 + |S| + vertex-cover number of E minus S.")
print(dict(sorted(counts.items())))
print("16-gate compulsory sets:", [
    [edge for j, edge in enumerate(EDGES) if mask >> j & 1]
    for mask, _, total in rows if total == 16])
