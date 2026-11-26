"""Enumerate fixed-pair read-2 profiles and separate them with nine continuations."""
from itertools import combinations, product

BUDGETS = tuple(product(range(3), repeat=2))


def minimize(points):
    points = set(points) & set(BUDGETS)
    return frozenset((a, b) for a, b in points if not any(
        (c, d) != (a, b) and c <= a and d <= b for c, d in points))


def meet(left, right):
    return minimize((a + c, b + d) for a, b in left for c, d in right)


def accepts_shift(profile, i, j):
    return any(a + 2 - i <= 2 and b + 2 - j <= 2 for a, b in profile)


def main():
    states = {frozenset({(1, 0)}), frozenset({(0, 1)})}
    while True:
        next_states = states | {value for p, q in product(states, repeat=2)
                                for value in (minimize(p | q), meet(p, q))}
        if next_states == states:
            break
        states = next_states
    assert len(states) == 19
    pairs = list(combinations(states, 2))
    assert all(any(accepts_shift(p, i, j) != accepts_shift(q, i, j)
                   for i, j in BUDGETS) for p, q in pairs)
    print(f"{len(states)} reachable profiles, {len(pairs)} separated unordered pairs")


if __name__ == "__main__":
    main()
