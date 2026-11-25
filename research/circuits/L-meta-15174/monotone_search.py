"""Decide a gate budget for a monotone function of two to six essential inputs.

A set bit at position r is the function value on input row r. Gates are
binary AND and OR. Wires may be reused. The search returns a netlist on
success, and exhausts the bounded state space on failure. Python 3.10+.
"""
import argparse
from functools import cache
from itertools import combinations


def boundary(table, n):
    if not 2 <= n <= 6 or not 0 <= table < 1 << (1 << n):
        raise ValueError("expected a truth table of two to six inputs")
    rows = range(1 << n)

    def value(r):
        return (table >> r) & 1

    minimal, maximal, essential = [], [], set()
    for r in rows:
        above = [r | (1 << i) for i in range(n) if not (r >> i) & 1]
        below = [r ^ (1 << i) for i in range(n) if (r >> i) & 1]
        for s in above:
            if value(r) > value(s):
                raise ValueError("truth table is not monotone")
            if value(r) != value(s):
                essential.add((s ^ r).bit_length() - 1)
        if value(r) and all(not value(s) for s in below):
            minimal.append(r)
        if not value(r) and all(value(s) for s in above):
            maximal.append(r)
    if len(essential) != n:
        raise ValueError("remove inessential inputs before searching")
    return minimal, maximal


def search(table, n, budget):
    """Return a witness of size at most budget, or None, and search statistics."""
    if budget < 0:
        raise ValueError("budget must be nonnegative")
    positive, negative = boundary(table, n)
    rows = positive + negative
    target = (1 << len(positive)) - 1
    inputs = tuple(sum(((r >> i) & 1) << j for j, r in enumerate(rows))
                   for i in range(n))
    all_pairs = (1 << (len(positive) * len(negative))) - 1

    @cache
    def separates(wire):
        # A monotone continuation needs a live wire that is 1 on the
        # positive row and 0 on the negative row for every directed pair.
        neg_zeros = (~(wire >> len(positive))) & ((1 << len(negative)) - 1)
        return sum(neg_zeros << (i * len(negative)) for i in range(len(positive))
                   if (wire >> i) & 1)

    @cache
    def solve(live, remaining):
        if target in live:
            return ()
        # After dead gates are removed, each currently live wire still leads
        # to the single output. A binary gate can reduce this count by at most one.
        if remaining == 0 or len(live) > remaining + 1:
            return None
        coverage = 0
        for wire in live:
            coverage |= separates(wire)
        if coverage != all_pairs:
            return None
        for i, j in combinations(range(len(live)), 2):
            a, b = live[i], live[j]
            rest = [w for k, w in enumerate(live) if k != i and k != j]
            for op, out in (("AND", a & b), ("OR", a | b)):
                # An existing wire with the same boundary values can serve
                # every future consumer of this gate.
                if out in live:
                    continue
                # Keep an operand precisely when it still has a later consumer.
                for retained in ((), (a,), (b,), (a, b)):
                    after = tuple(sorted([*rest, *retained, out]))
                    if len(after) <= remaining:
                        tail = solve(after, remaining - 1)
                        if tail is not None:
                            return ((op, a, b, out),) + tail
        return None

    path = solve(tuple(sorted(inputs)), budget)
    states = solve.cache_info().misses
    if path is None:
        return None, states
    wire_numbers = {word: i for i, word in enumerate(inputs)}
    gates = []
    for op, a, b, out in path:
        gates.append((op, wire_numbers[a], wire_numbers[b]))
        wire_numbers[out] = n + len(gates) - 1
    # The last gate makes target available. Cross-check every input row.
    for r in range(1 << n):
        values = [(r >> i) & 1 for i in range(n)]
        for op, a, b in gates:
            values.append(values[a] & values[b] if op == "AND" else values[a] | values[b])
        assert values[-1] == (table >> r) & 1
    return gates, states


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=lambda s: int(s, 0))
    parser.add_argument("inputs", type=int)
    parser.add_argument("budget", type=int)
    args = parser.parse_args()
    if args.budget < 0:
        parser.error("budget must be nonnegative")
    gates, states = search(args.table, args.inputs, args.budget)
    print(f"{states} states; " + ("no circuit in budget" if gates is None else f"{len(gates)} gates: {gates}"))
