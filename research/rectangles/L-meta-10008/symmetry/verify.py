#!/usr/bin/env python3
"""Replay cyclic lower bounds and the 22-orbit-cover optimum for a group of order 60."""
from functools import lru_cache

MATRIX = (1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420,
 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336,
 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369,
 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736)
GENERATORS = {
    "tor24": (
        (3, 5, 18, 14, 26, 24, 22, 0, 2, 19, 7, 1, 10, 21, 6, 17, 4, 8, 20, 30, 9, 15, 23,
         29, 27, 11, 13, 25, 28, 16, 12),
        (0, 17, 20, 1, 23, 11, 7, 9, 25, 13, 21, 30, 28, 26, 6, 8, 14, 27, 5, 16, 10, 12, 24,
         3, 15, 19, 29, 4, 22, 18, 2),
    ),
    "j20": (
        (2, 1, 14, 13, 17, 25, 8, 20, 19, 26, 0, 5, 4, 15, 16, 6, 18, 10, 9, 22, 21, 23, 29,
         7, 11, 27, 30, 24, 28, 12, 3),
        (0, 3, 19, 23, 1, 7, 9, 8, 21, 20, 12, 24, 14, 15, 26, 25, 30, 4, 11, 10, 22, 5, 13,
         17, 16, 29, 28, 27, 18, 2, 6),
    ),
    "s1101": (
        (15, 1, 8, 14, 0, 27, 21, 19, 17, 18, 28, 25, 22, 12, 30, 16, 20, 10, 26, 3, 4, 13,
         6, 9, 5, 24, 29, 11, 2, 23, 7),
        (0, 28, 18, 6, 22, 27, 14, 21, 7, 3, 20, 26, 16, 25, 23, 24, 17, 1, 29, 11, 19, 5,
         15, 9, 30, 2, 10, 8, 12, 13, 4),
    ),
    "s0411": (
        (24, 28, 8, 3, 27, 0, 7, 22, 17, 4, 1, 29, 19, 30, 12, 26, 20, 2, 16, 14, 18, 13, 6,
         11, 5, 15, 25, 9, 10, 23, 21),
        (4, 14, 29, 16, 30, 27, 28, 23, 3, 7, 2, 26, 6, 11, 21, 24, 8, 5, 18, 25, 19, 1, 15,
         9, 22, 20, 13, 17, 12, 10, 0),
    ),
}
N = len(MATRIX)
ALL = (1 << N) - 1
IDENTITY = (tuple(range(N)), tuple(range(N)))
WITNESS = [(1365255403, 21266432), (1075429531, 268636162), (51380741, 36052012)]


def invariant(condition):
    if not condition:
        raise ValueError("certificate check failed")


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def compose(first, second):
    return tuple(tuple(b[i] for i in a) for a, b in zip(first, second))


def generate(generators):
    queue = [IDENTITY]
    seen = set(queue)
    for g in queue:
        for h in generators:
            gh = compose(g, h)
            if gh not in seen:
                queue.append(gh)
                seen.add(gh)
    return queue


def image(mask, permutation):
    return sum(1 << permutation[i] for i in bits(mask))


def orbit(rectangle, group):
    rows, columns = rectangle
    return {(image(rows, p), image(columns, q)) for p, q in group}


def validate_generators():
    for p, q in GENERATORS.values():
        invariant(sorted(p) == sorted(q) == list(range(N)))
        invariant(all(image(mask, q) == MATRIX[p[i]] for i, mask in enumerate(MATRIX)))


def cyclic_bound(name, order, primes):
    group = generate([GENERATORS[name]])
    invariant(len(group) == order)
    invariant(not (MATRIX[0] >> 10 & 1))
    for prime in primes:
        subgroup = group[::order // prime]
        invariant(len(subgroup) == prime)
        invariant(any(MATRIX[p[0]] >> q[10] & 1 for p, _ in subgroup for _, q in subgroup))
    invariant(any(all(p[i] == i for p, _ in group) for i in range(N)))
    invariant(all(q[0] == 0 for _, q in group))
    transpose = [sum(((row >> j) & 1) << i for i, row in enumerate(MATRIX))
                 for j in range(N)]
    for masks in (MATRIX, transpose):
        invariant(len(set(masks)) == N)
        invariant(all(mask.bit_count() == 6 for mask in masks))
    print(f"{name} invariant cover lower bound: {order + 2}")
    if name == "tor24":
        reps = [(20119655, 537280524), (1962932189, 1), (268435456, 2004746213)]
        sets = [orbit(r, group) for r in reps]
        invariant([len(s) for s in sets] == [24, 1, 1])
        verify_cover(set.union(*sets), 26)
        print("Order 24 invariant optimum: 26")


def verify_cover(family, size):
    invariant(len(family) == size)
    for i, row in enumerate(MATRIX):
        columns = 0
        for a, b in family:
            if a >> i & 1:
                columns |= b
        invariant(columns == ALL ^ row)


def prime_subgroup_representatives(group):
    """Choose one generator per conjugacy class of prime-order subgroups."""
    seen = {IDENTITY}
    for g in group:
        if g in seen:
            continue
        cyclic = generate([g])
        if len(cyclic) not in (2, 3, 5):
            continue
        for h in group:
            inv = tuple(tuple(p.index(i) for i in range(N)) for p in h)
            seen.update(compose(compose(h, a), inv) for a in cyclic)
        yield g


def maximal_rectangles_fixed_by(permutation):
    """A fixed row set is a union of permutation cycles. Compute its maximal closure."""
    unseen = set(range(N))
    intersections = {ALL}
    while unseen:
        start = next(iter(unseen))
        current = start
        allowed = ALL
        while current in unseen:
            unseen.remove(current)
            allowed &= ~MATRIX[current]
            current = permutation[current]
        intersections |= {c & allowed for c in intersections}
    for columns in intersections:
        rows = sum(1 << i for i, mask in enumerate(MATRIX) if not mask & columns)
        if rows and columns:
            yield rows, columns


def edge_orbits(group):
    labels = {}
    count = 0
    for i, row in enumerate(MATRIX):
        for j in bits(ALL ^ row):
            if (i, j) in labels:
                continue
            for p, q in group:
                labels[p[i], q[j]] = count
            count += 1
    return labels, count


def verify_order60():
    group = generate([GENERATORS["s1101"], GENERATORS["s0411"]])
    invariant(len(group) == 60)
    labels, count = edge_orbits(group)
    seen = set()
    candidates = []
    for g in prime_subgroup_representatives(group):
        for rectangle in maximal_rectangles_fixed_by(g[0]):
            if rectangle in seen:
                continue
            family = orbit(rectangle, group)
            seen.update(family)
            if len(family) > 21:
                continue
            rows, columns = rectangle
            indices = {labels[i, j] for i in bits(rows) for j in bits(columns)}
            candidates.append((len(family), sum(1 << i for i in indices)))
    invariant(count == 21 and len(candidates) == 241)
    options = [[(cost, mask) for cost, mask in candidates if mask >> i & 1]
               for i in range(count)]
    full = (1 << count) - 1

    @lru_cache(None)
    def can_cover(covered, remaining):
        if covered == full:
            return True
        missed = min(bits(full ^ covered),
                     key=lambda i: sum(cost <= remaining for cost, _ in options[i]))
        return any(cost <= remaining and can_cover(covered | mask, remaining - cost)
                   for cost, mask in options[missed])

    invariant(not can_cover(0, 21))
    families = [orbit(r, group) for r in WITNESS]
    invariant([len(s) for s in families] == [10, 6, 6])
    family = set.union(*families)
    verify_cover(family, 22)
    print(f"Order 60 invariant optimum: 22, with {len(candidates)} candidate orbits of cost at most 21")


if __name__ == "__main__":
    validate_generators()
    cyclic_bound("tor24", 24, (2, 3))
    cyclic_bound("j20", 20, (2, 5))
    verify_order60()
