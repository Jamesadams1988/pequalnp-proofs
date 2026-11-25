"""Measure the unrestricted and monotone sizes of all one-pin faces of a six-input table.

For each five-input face, generate monotone formulas through seven gates for upper
bounds and search unrestricted circuits through six gates for exact lower bounds.
Both constants are free during the lower-bound search. Bit r is the output on
row r, with input 0 in the least significant bit. Python 3.10+.
"""
import argparse
from itertools import combinations

TARGET = (4008372970 << 32) + 4007717088
MASK = (1 << 32) - 1
INPUTS = tuple(sum((row >> i & 1) << row for row in range(32)) for i in range(5))


def faces(table):
    if not 0 <= table < 1 << 64:
        raise ValueError("expected an unsigned six-input truth table")
    for i in range(6):
        for b in (0, 1):
            rows = (r for r in range(64) if r >> i & 1 == b)
            yield i, b, sum((table >> r & 1) << j for j, r in enumerate(rows))


def monotone_formulas():
    # Leaves a..e refer to the remaining inputs in ascending original order.
    levels = [set(INPUTS)]
    formulas = {t: (0, name) for t, name in zip(INPUTS, "abcde")}
    for size in range(1, 8):
        added = set()
        for i in range((size - 1) // 2 + 1):
            for x in sorted(levels[i]):
                for y in sorted(levels[size - 1 - i]):
                    for table, op in ((x & y, "&"), (x | y, "|")):
                        if table not in formulas:
                            formulas[table] = (size, f"({formulas[x][1]}{op}{formulas[y][1]})")
                            added.add(table)
        levels.append(added)
    return formulas


def next_wires(wires):
    generated = {MASK ^ x for x in wires}
    for x, y in combinations(wires, 2):
        generated.add(x & y)
        generated.add(x | y)
    # A gate producing a wire already available can be bypassed.
    return generated.difference(wires)


def two_gates(wires, new, target):
    # If both operands come from the first gate they are the same wire.
    if MASK ^ target in new:
        return True
    for old in wires:
        if old & target == old and any(old | x == target for x in new if x & target == x):
            return True
        if old & target == target and any(old & x == target for x in new if x & target == target):
            return True
    return False


def unrestricted_sizes(targets):
    """Exact sizes up to six with free constants. Absence gives a lower bound of seven."""
    initial = frozenset((*INPUTS, 0, MASK))
    states = {initial}
    best = {t: 0 for t in targets if t in initial}
    for depth in range(5):
        following = set()
        for wires in states:
            new = next_wires(wires)
            for target in targets:
                if best.get(target, 7) <= depth + 1 and depth:
                    # The preceding layer has already checked all circuits of this size.
                    continue
                if target in new:
                    best[target] = min(best.get(target, 7), depth + 1)
                elif best.get(target, 7) > depth + 2 and two_gates(wires, new, target):
                    best[target] = depth + 2
            if depth < 4:
                following.update(wires | {x} for x in new)
        states = following
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", nargs="?", type=lambda s: int(s, 0), default=TARGET)
    table = parser.parse_args().table
    rows = list(faces(table))
    formulas = monotone_formulas()
    control = (INPUTS[0] & INPUTS[1]) | (INPUTS[2] & INPUTS[3])
    targets = {t for _, _, t in rows} | {control, MASK ^ INPUTS[0], INPUTS[0]}
    sizes = unrestricted_sizes(targets)
    if (sizes.get(control), sizes.get(MASK ^ INPUTS[0]), sizes.get(INPUTS[0])) != (3, 1, 0):
        raise RuntimeError("unrestricted search failed its known-size controls")
    print("input bit   table       lower  monotone formula upper and witness")
    profile = []
    for i, b, t in rows:
        lower = sizes.get(t, 7)
        upper, formula = formulas.get(t, (None, ""))
        if upper is not None and lower > upper:
            raise RuntimeError("lower and upper bounds disagree")
        print(f"x{i}    {b}     0x{t:08x}  {lower:>3}   {str(upper):>4}  {formula}")
        profile.append((lower, upper))
    if table == TARGET:
        expected = [3, 4, 4, 5, 7, 1, 4, 6, 6, 5, 6, 4]
        if profile != [(n, n) for n in expected]:
            raise RuntimeError("face sizes differ from the reference profile")


if __name__ == "__main__":
    main()
