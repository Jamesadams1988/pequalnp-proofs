"""Reproduce the maximal negative tests and factor-support bounds for L-meta-1988."""
from collections import Counter
from itertools import combinations
from math import comb

N = 13
D = {0, 1, 3, 9}
SIDE = (1 << N) - 1
NEIGHBORS = [sum(1 << line for line in range(N) if (point + line) % N in D)
             for point in range(N)]


def avoiding(points):
    return sum(1 << line for line in range(N) if not points & NEIGHBORS[line])


def maximal_negatives():
    result = set()
    for points in range(1 << N):
        lines = avoiding(points)
        if avoiding(lines) == points:
            result.add(points | (lines << N))
    tests = set()
    for side in range(1 << N):
        if side.bit_count() <= 3:
            other = avoiding(side)
            tests.update((side | (other << N), other | (side << N)))
    assert result == tests and len(result) == 704
    return sorted(result)


def audit_ignored_variables(negatives):
    # Bit i records whether the ith maximal negative omits a given vertex.
    all_rows = (1 << len(negatives)) - 1
    omits = [sum(1 << i for i, row in enumerate(negatives) if not row & (1 << v))
             for v in range(2 * N)]
    closed_neighborhoods = {(1 << i) | (nb << N) for i, nb in enumerate(NEIGHBORS)}
    closed_neighborhoods |= {nb | (1 << (N + i)) for i, nb in enumerate(NEIGHBORS)}
    print('marked vertices | sets tested | least number of disjoint maximal negatives | hitting sets')
    for size in range(1, 6):
        hits = set()
        least = len(negatives)
        for vertices in combinations(range(2 * N), size):
            remaining = all_rows
            for vertex in vertices:
                remaining &= omits[vertex]
            least = min(least, remaining.bit_count())
            if not remaining:
                hits.add(sum(1 << v for v in vertices))
        assert hits == (closed_neighborhoods if size == 5 else set())
        print(size, comb(2 * N, size), least, len(hits), sep=' | ')


def audit_two_outputs(negatives):
    # m(U) counts the maximal negatives containing every omitted coordinate U.
    multiplicities = Counter()
    for negative in negatives:
        subset = negative
        while subset:
            multiplicities[subset] += 1
            subset = (subset - 1) & negative
    # Independently count independent subsets by choosing a point set, then
    # choosing each line from its avoiding set.
    by_size = Counter()
    for points in range(1 << N):
        lines = avoiding(points).bit_count()
        for k in range(lines + 1):
            by_size[points.bit_count() + k] += comb(lines, k)
    print('omissions | independent choices | max m(U) | required rejections by sibling')
    for size in range(1, max(by_size) + 1):
        values = [count for subset, count in multiplicities.items() if subset.bit_count() == size]
        assert len(values) == by_size[size]
        best = max(values)
        print(size, len(values), best, len(negatives) - best, sep=' | ')


if __name__ == '__main__':
    assert all(nb.bit_count() == 4 for nb in NEIGHBORS)
    assert all((a & b).bit_count() == 1 for a, b in combinations(NEIGHBORS, 2))
    rows = maximal_negatives()
    print('Maximal negatives', len(rows))
    audit_ignored_variables(rows)
    audit_two_outputs(rows)
