"""Check exact gate counts for L-meta-13194 with Python's standard library.

A wire is its entire truth table. The lower-bound search allows free true and
false. This includes missing wires, constants, copies and repeated operands in
the Lean model. A binary AND/OR or unary NOT costs one gate.

Pinning an essential input saves at least one gate if the restricted function
is nonconstant. Prune unused gates and bypass copies and constant outputs first.
The output cannot be the input being pinned. An earliest gate directly using
that input therefore exists. After pinning, NOT there is constant, and AND/OR
there is a constant or a copy. Bypassing it gives the promised saving. This
argument also applies when free constants are available.

Here the two pins leave threshold two on four inputs. The search below covers
every unrestricted circuit for that function with at most six gates. Thus the
six-input function requires at least nine gates, even with free constants.
"""
from itertools import combinations

TARGET = (4294901482 << 32) + 4278124266
K4 = sum((row.bit_count() >= 2) << row for row in range(16))
GATES = (
    ("or", 1, 2), ("or", 3, 4), ("and", 1, 2), ("and", 3, 4),
    ("and", 6, 7), ("and", 5, 9), ("or", 8, 10), ("or", 11, 12),
    ("or", 0, 13),
)


def input_tables(n):
    return tuple(sum(((row >> bit) & 1) << row for row in range(1 << n))
                 for bit in range(n))


def two_pin_k4_certificates(table):
    """Return ordered pairs ((input, bit), (input, bit)) for a six-input table.

    Each selected input is essential immediately before its pin. Both
    restricted functions are nonconstant and the final table is K4.
    """
    if not 0 <= table < 1 << 64:
        raise ValueError("expected an unsigned 64-bit truth table")

    def live_pins(fixed):
        pinned_inputs = {i for i, _ in fixed}
        rows = [r for r in range(64) if all(r >> i & 1 == b for i, b in fixed)]
        for i in range(6):
            if i in pinned_inputs:
                continue
            cuts = []
            for b in (0, 1):
                selected = [r for r in rows if r >> i & 1 == b]
                # Ascending row order preserves the numbering of remaining inputs.
                cuts.append(sum((table >> r & 1) << k for k, r in enumerate(selected)))
            if cuts[0] != cuts[1]:  # the input is essential under the earlier pin(s)
                full = (1 << (len(rows) // 2)) - 1
                for b, cut in enumerate(cuts):
                    if 0 < cut < full:
                        yield (i, b), cut

    return {(first, second) for first, _ in live_pins(())
            for second, cut in live_pins((first,)) if cut == K4}


def check_witness_and_restrictions():
    wires = list(input_tables(6))
    assert len(GATES) == 9
    for op, i, j in GATES:
        assert op in ("and", "or")
        assert 0 <= i < len(wires) and 0 <= j < len(wires)
        a, b = wires[i], wires[j]
        wires.append(a & b if op == "and" else a | b)
    assert wires[14] == TARGET
    print(f"All 64 rows agree with the nine-gate monotone circuit ({TARGET:#018x}).")

    def output(row):
        return (TARGET >> row) & 1

    assert output(0) == 0 and output(1) == 1  # x0 is essential.
    assert output(24) == 0 and output(56) == 1  # x5 is essential with x0 = 0.
    pinned = sum(output((row << 1) | 32) << row for row in range(16))
    assert pinned == K4
    expected = {((0, 0), (5, 1)), ((5, 1), (0, 0))}
    assert two_pin_k4_certificates(TARGET) == expected
    print(f"Both orders of x0 = 0, x5 = 1 give {pinned:#06x}, with two essential pins"
          " and nonconstant restrictions after each pin.")

    # Repeat K4 over all settings of the last two inputs.
    dummy = sum(K4 << offset for offset in range(0, 64, 16))
    x4, x5 = input_tables(6)[4:]
    positive = (dummy | x4) & x5
    assert two_pin_k4_certificates(positive) == {((4, 0), (5, 1)), ((5, 1), (4, 0))}
    # With two ignored inputs every pinning of those inputs gives K4, but saves no gates.
    assert not two_pin_k4_certificates(dummy)
    print("Detector controls passed for a gated K4 and a K4 with two ignored inputs.")


def new_wires(wires, mask):
    results = {mask ^ a for a in wires}
    for a, b in combinations(wires, 2):
        results.add(a & b)
        results.add(a | b)
    return results.difference(wires)


def reaches_in_two(wires, next_values, goal, mask):
    # In the second gate only one distinct input can come from the first gate.
    if goal in wires or goal in next_values or mask ^ goal in next_values:
        return True
    low = [a for a in wires if a & goal == a]
    high = [a for a in wires if a & goal == goal]
    for b in next_values:
        if b & goal == b and any(a | b == goal for a in low):
            return True
        if b & goal == goal and any(a & b == goal for a in high):
            return True
    return False


def excludes_six(goal):
    mask = (1 << 16) - 1
    initial = frozenset((*input_tables(4), 0, mask))
    states = {initial}
    for depth in range(5):
        print(f"Checking {len(states):,} distinct wire sets at gate count {depth}.", flush=True)
        later = set()
        for wires in states:
            # Recomputing an available truth table can be bypassed at no cost.
            one = new_wires(wires, mask)
            if reaches_in_two(wires, one, goal, mask):
                return False
            if depth < 4:
                later.update(wires | {w} for w in one)
        states = later
    return True


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Verification requires assertions. Run Python without -O.")
    check_witness_and_restrictions()
    a, b, c, d = input_tables(4)
    assert not excludes_six((a & b) | (c & d)), "Missed a known three-gate circuit"
    print("Search control found a circuit for (x0 AND x1) OR (x2 AND x3).")
    assert excludes_six(K4), "Found a threshold circuit with at most six gates"
    print("No unrestricted circuit of at most six gates computes the restriction.")
    print("The unrestricted and monotone minima for the original table are both nine.")
