"""Count the maximal false assignments and essential raw clauses of PG(2,q) incidence."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "packed"))
from packed import plane


def closure_enumeration(rows):
    n = len(rows)
    universe = (1 << n) - 1
    neighborhoods = [sum(1 << line for line in row) for row in rows]
    unions = {0}
    for neighbors in neighborhoods:
        unions |= {old | neighbors for old in unions}
    maximal = set()
    for union in unions:
        points = 0
        reconstructed = 0
        for i, neighbors in enumerate(neighborhoods):
            if neighbors & ~union == 0:
                points |= 1 << i
                reconstructed |= neighbors
        assert reconstructed == union
        maximal.add((points, universe ^ union))
    assert len(unions) == len(maximal)
    return maximal


def direct_point_subsets(rows):
    n = len(rows)
    all_lines = set(range(n))
    found = set()
    for size in range(n + 1):
        for chosen in combinations(range(n), size):
            lines = all_lines.difference(*(rows[i] for i in chosen))
            if all(rows[i] & lines for i in range(n) if i not in chosen):
                found.add((sum(1 << i for i in chosen), sum(1 << j for j in lines)))
    return found


def direct_assignments(rows):
    n = len(rows)
    edges = [(1 << i) | (1 << (n + j)) for i, row in enumerate(rows) for j in row]
    false = {s for s in range(1 << (2*n)) if all(s & e != e for e in edges)}
    maximal = {s for s in false if all((s | (1 << i)) not in false
                                      for i in range(2*n) if not s >> i & 1)}
    return {(s & ((1 << n) - 1), s >> n) for s in maximal}


def main():
    for q in (2, 3, 4):
        rows = plane(q)
        n = len(rows)
        maximal = closure_enumeration(rows)
        if q <= 3:
            assert maximal == direct_point_subsets(rows)
        if q == 2:
            assert maximal == direct_assignments(rows)
        width = Counter(2*n - p.bit_count() - l.bit_count() for p, l in maximal)
        print(f"q={q}, N={n}, maximal false assignments = essential clauses = {len(maximal)}")
        print("clause width -> count:", dict(sorted(width.items())))


if __name__ == "__main__":
    main()
