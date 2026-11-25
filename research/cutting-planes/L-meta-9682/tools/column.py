"""Enumerate cutting-planes lines supported by disjoint K4 collision clauses.

A line (a,b,c,d,k) represents ax+by+cz+dw <= k. Each of the six edge
axioms may occur at most once in the tree. Addition requires disjoint
edge sets. Positive divisors must divide every coefficient. The RHS uses
floor division. Multiplication and extra axioms are outside this model.
"""
from itertools import combinations
from math import gcd


EDGES = list(combinations(range(4), 2))
CAPACITY = (1, 1, 1, 1, 1)


def reachable():
    levels = [set() for _ in range(1 << len(EDGES))]
    for i, (u, v) in enumerate(EDGES):
        levels[1 << i].add(tuple(int(j in (u, v)) for j in range(4)) + (1,))
    for mask in range(1, len(levels)):
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if left < right:
                for a in levels[left]:
                    for b in levels[right]:
                        levels[mask].add(tuple(x + y for x, y in zip(a, b)))
            left = (left - 1) & mask
        for a in list(levels[mask]):
            divisor = gcd(*a[:4])
            for d in range(2, divisor + 1):
                if divisor % d == 0:
                    levels[mask].add(tuple(v // d for v in a))
        # Successive divisions introduce no extra lines here: floor(floor(x/i)/j)
        # equals floor(x/(i*j)), and i*j divides every original coefficient.
    return levels


if __name__ == '__main__':
    levels = reachable()
    print('Nonempty edge sets:', sum(bool(s) for s in levels))
    print('Distinct (edge set, inequality) pairs:', sum(map(len, levels)))
    print('Attainable all-four RHS values using all six edges:',
          sorted(a[4] for a in levels[63] if a[:4] == (1, 1, 1, 1)))
    assert not any(CAPACITY in bucket for bucket in levels)
