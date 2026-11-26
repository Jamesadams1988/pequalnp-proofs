"""Verify the three-edge path implication for every four-variable read-once function."""
from functools import lru_cache


@lru_cache(None)
def functions(available):
    full = (1 << 16) - 1
    values = {0, full}
    for v in range(4):
        if available >> v & 1:
            values.add(sum((s >> v & 1) << s for s in range(16)))
    left = (available - 1) & available
    while left:
        right = available ^ left
        if left < right:
            for a in functions(left):
                for b in functions(right):
                    values.update((a & b, a | b))
        left = (left - 1) & available
    return values


def accepts(table, assignment):
    return bool(table >> assignment & 1)


def main():
    all_tables = functions(15)
    candidates = [f for f in all_tables if not any(accepts(f, 1 << v) for v in range(4))
                  and all(accepts(f, edge) for edge in (3, 6, 12))]
    if (len(all_tables), len(candidates)) != (102, 1):
        raise ValueError("unexpected count of read-once functions or path witnesses")
    if any(not accepts(f, 9) for f in candidates):
        raise ValueError("a read-once function rejects the endpoints of an accepted three-edge path")
    print(f"{len(all_tables)} read-once truth tables, {len(candidates)} satisfy the path hypotheses.")
    print("Every qualifying function accepts both endpoints of the path together.")


if __name__ == "__main__":
    main()
