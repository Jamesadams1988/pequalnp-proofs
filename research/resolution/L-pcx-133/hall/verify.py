"""Count exact covers by the sixty 3-pigeons-in-2-holes Hall clauses of BPHP(5,2)."""
from collections import Counter
from itertools import combinations, product

PIGEONS = range(5)
HOLES = range(4)
POINTS = list(product(HOLES, repeat=5))
CRITICAL = [x for x in POINTS if sorted(Counter(x).values()) == [1, 1, 1, 2]]
HALL = list(product(combinations(PIGEONS, 3), combinations(HOLES, 2)))


def forbidden(clause, assignment):
    pigeons, holes = clause
    return all(assignment[i] in holes for i in pigeons)


def coverage_mask(clause, assignments):
    return sum(1 << i for i, x in enumerate(assignments) if forbidden(clause, x))


def unique_collision(assignment):
    pairs = [(p, q, assignment[p]) for p, q in combinations(PIGEONS, 2)
             if assignment[p] == assignment[q]]
    assert len(pairs) == 1
    return pairs[0]


def full_check():
    assert len(POINTS) == 1024 and len(CRITICAL) == 240 and len(HALL) == 60
    axiom = list(map(unique_collision, CRITICAL))
    assert len(set(axiom)) == 40
    critical_mask = [coverage_mask(clause, CRITICAL) for clause in HALL]
    all_mask = [coverage_mask(clause, POINTS) for clause in HALL]
    assert all(mask.bit_count() == 12 for mask in critical_mask)
    for mask in critical_mask:
        collisions = Counter(axiom[i] for i in range(240) if mask >> i & 1)
        assert len(collisions) == 6 and all(count == 2 for count in collisions.values())

    incidence = [[i for i, mask in enumerate(critical_mask) if mask >> j & 1]
                 for j in range(len(CRITICAL))]
    solutions = set()

    def search(uncovered, chosen):
        if not uncovered:
            assert len(chosen) == 20
            solutions.add(frozenset(chosen))
            return
        # Branch on a still-uncovered assignment. At most 20 clauses can cover
        # all 240 inputs only if every chosen mask is disjoint from earlier masks.
        best = None
        for j, buckets in enumerate(incidence):
            if not (uncovered >> j & 1):
                continue
            options = [i for i in buckets if critical_mask[i] & ~uncovered == 0]
            if not options:
                return
            if best is None or len(options) < len(best):
                best = options
        for i in best:
            search(uncovered ^ critical_mask[i], chosen + [i])

    search((1 << len(CRITICAL)) - 1, [])
    expected = set()
    for k in (1, 2, 3):
        left = (0, k)
        right = tuple(h for h in HOLES if h not in left)
        expected.add(frozenset(i for i, (_, h) in enumerate(HALL) if h in (left, right)))
    assert solutions == expected
    for solution in solutions:
        covered = 0
        for i in solution:
            covered |= all_mask[i]
        assert covered == (1 << len(POINTS)) - 1
    print('1,024 assignments; 240 unique collisions across 40 distinct axioms.')
    print('60 Hall clauses; each excludes 12 unique collisions from 6 distinct axioms.')
    print('Minimum cover size: 20. All 3 optimal covers verified on all 1,024 assignments.')
    print('Hole partitions: 01|23, 02|13, 03|12.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Enable assertions by running Python without -O.')
    full_check()
