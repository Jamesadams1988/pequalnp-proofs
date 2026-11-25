"""Enumerate labelled monotone functions built by adjoining fresh outer gates.

Each of the original inputs can occupy any of the remaining coordinates.
Use the given core and its De Morgan dual. Each new input is conjoined or
disjoined with the entire preceding function and appears exactly once.
"""
import argparse
from functools import cache
from itertools import combinations, permutations, product


def dual(table, n):
    return sum((1 ^ ((table >> ((1 << n) - 1 - r)) & 1)) << r
               for r in range(1 << n))


@cache
def column(n, i):
    return sum(((r >> i) & 1) << r for r in range(1 << n))


def relabel(table, n, labels):
    result = 0
    for r in range(1 << n):
        source_row = sum(((r >> i) & 1) << j for j, i in enumerate(labels))
        result |= ((table >> source_row) & 1) << r
    return result


def extensions(table, n, count):
    total = n + count
    if n < 1 or count < 0 or total > 8 or not 0 <= table < (1 << (1 << n)):
        raise ValueError("expected a valid table on a total of one through eight inputs")
    # Deduplicate the core orbit before considering positions for extra inputs.
    orbit = {relabel(t, n, p) for t in (table, dual(table, n))
             for p in permutations(range(n))}
    functions = set()
    for fresh in combinations(range(total), count):
        labels = tuple(i for i in range(total) if i not in fresh)
        for t in orbit:
            lifted = relabel(t, total, labels)
            for order in permutations(fresh):
                for gates in product(("AND", "OR"), repeat=count):
                    out = lifted
                    for i, gate in zip(order, gates):
                        wire = column(total, i)
                        out = out & wire if gate == "AND" else out | wire
                    functions.add(out)
    return functions


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=lambda s: int(s, 0))
    parser.add_argument("inputs", type=int)
    parser.add_argument("fresh", type=int)
    parser.add_argument("--find", type=lambda s: int(s, 0))
    args = parser.parse_args()
    tables = extensions(args.table, args.inputs, args.fresh)
    print(f"{len(tables)} distinct labelled truth tables")
    if args.find is not None:
        print("present" if args.find in tables else "absent")
