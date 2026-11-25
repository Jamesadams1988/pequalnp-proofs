"""Bound arbitrary-scalar read-once CP trees after three mixed triangle cuts.

A positive scale u indexes a bound on the integer RHS with coefficient vector
u * V_S / g_S. WILDCARD indexes a normalized bound B: for arbitrary positive
scale lambda on V_S, the RHS is at most lambda * B. See mixed-triangles.md.
"""
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import ceil, floor, gcd
from sys import argv
from time import monotonic

import sympy

WILDCARD = -1


def premises(pivots):
    vectors, bounds, weights = [], [], []
    for hole, pivot in enumerate(pivots):
        for star in (False, True):
            vectors.append(tuple(
                -(1 + 2 * (pigeon == pivot) if star else int(pigeon != pivot))
                if column == hole else 0
                for column in range(3) for pigeon in range(4)
            ))
            bounds.append(-3 if star else -1)
            weights.append(1 if star else 2)
    for pigeon in range(4):
        vectors.append(tuple(int(i == pigeon) for _ in range(3) for i in range(4)))
        bounds.append(1)
        weights.append(3)
    kernel = sympy.Matrix(vectors).T.nullspace()
    assert len(kernel) == 1 and list(3 * kernel[0]) == weights
    return vectors, bounds, weights


def subset_scales(vectors, weights):
    sums = {0: (0,) * 12}
    scales = {}
    full = (1 << len(vectors)) - 1
    for subset in range(1, full + 1):
        bit = subset & -subset
        i = bit.bit_length() - 1
        sums[subset] = tuple(a + weights[i] * b for a, b in zip(sums[subset ^ bit], vectors[i]))
        scales[subset] = reduce(gcd, sums[subset], 0)
    assert scales[full] == 0 and all(scales[s] > 0 for s in range(1, full))
    return scales


def record(bounds, scale, rhs):
    if scale not in bounds or rhs > bounds[scale]:
        bounds[scale] = rhs


def add_children(out, left, right, gl, gr, parent):
    # An integer scale on one side fixes lambda, hence the scale on the other.
    for u, b in left.items():
        if u == WILDCARD:
            for v, c in right.items():
                if v == WILDCARD:
                    record(out, WILDCARD, b + c)
                else:
                    lam = Fraction(v, gr)
                    result = lam * parent
                    if result.denominator == 1:
                        record(out, int(result), floor(lam * b) + c)
        else:
            lam = Fraction(u, gl)
            result = lam * parent
            if result.denominator != 1:
                continue
            if WILDCARD in right:
                record(out, int(result), b + floor(lam * right[WILDCARD]))
            partner = lam * gr
            if partner.denominator == 1 and int(partner) in right:
                record(out, int(result), b + right[int(partner)])


def unary(out, states, divisor):
    for u, b in states.items():
        if u == WILDCARD:
            # ceil(mu*r)/mu <= ceil(r) for every positive integer mu.
            # This bound also covers a multiplication, which preserves r.
            record(out, WILDCARD, divisor * ceil(Fraction(b, divisor)))
        else:
            for d in range(2, u + 1):
                if u % d == 0:
                    record(out, u // d, -((-b) // d))
            record(out, WILDCARD, Fraction(b * divisor, u))


def run(pivots, budget):
    if len(pivots) != 3 or len(set(pivots)) < 2 or any(p not in range(4) for p in pivots):
        raise ValueError("supply three pigeon indices of a mixed triangle pattern")
    if budget < 0:
        raise ValueError("supply a nonnegative unary budget")
    vectors, bounds, weights = premises(pivots)
    scales = subset_scales(vectors, weights)
    n = len(vectors)
    full = (1 << n) - 1
    levels = {}
    for size in range(1, n + 1):
        for leaves in combinations(range(n), size):
            subset = sum(1 << i for i in leaves)
            entries = [{} for _ in range(budget + 1)]
            if size == 1:
                i = leaves[0]
                entries[0][scales[subset] // weights[i]] = bounds[i]
            else:
                left = (subset - 1) & subset
                while left:
                    right = subset ^ left
                    if left < right:
                        for x, ls in enumerate(levels[left]):
                            for y, rs in enumerate(levels[right][:budget + 1 - x]):
                                add_children(entries[x + y], ls, rs, scales[left],
                                             scales[right], scales[subset])
                    left = (left - 1) & subset
            if subset != full:
                for cost in range(budget):
                    unary(entries[cost + 1], entries[cost], scales[subset])
            levels[subset] = entries
    return [(entry.get(0), entry.get(WILDCARD)) for entry in levels[full]]


if __name__ == "__main__":
    pivots = list(map(int, argv[1]))
    budget = int(argv[2])
    start = monotonic()
    print("pivots", pivots, "extra unary", budget, "with unbounded multipliers and divisors")
    print("fixed RHS and wildcard normalized bound at zero by unary count",
          run(pivots, budget), round(monotonic() - start, 2))
