"""Verify the 64-gate prefix on all 2^26 inputs, in 8192 bit-parallel batches."""
from collections import Counter
from itertools import combinations

N = 13
D = (0, 1, 3, 9)
edges = {(p, l) for p in range(N) for l in range(N) if (p + l) % N in D}
near = [sorted(l for pp, l in edges if pp == p) for p in range(N)]
points = set(range(N))
assert len(edges) == 52 and all(len(lines) == 4 for lines in near)
assert all(len(set(near[p]) & set(near[q])) == 1 for p, q in combinations(points, 2))
assert all((p, -p % N) in edges for p in points)
gates = []


def emit(op, left, right):
    new_wire = 2 * N + len(gates)
    assert 0 <= left < new_wire and 0 <= right < new_wire
    gates.append((op, left, right))
    return new_wire


def or_of(wires):
    head, *tail = wires
    for w in tail:
        head = emit("or", head, w)
    return head


def line_sum(p):
    return or_of([N + l for l in near[p]])


common = or_of([emit("and", p, line_sum(p)) for p in range(1, N)])
assert len(gates) == 59
q2 = line_sum(0)
out1, out2 = emit("or", common, 0), emit("or", common, q2)
assert len(gates) == 64 and (out1, out2) == (88, 89)
assert Counter(op for op, _, _ in gates) == {"or": 52, "and": 12}

# Bit L of one packed wire contains its value on the line assignment L.
bits = 1 << N
full_word = (1 << bits) - 1
line_wires = [sum(1 << L for L in range(bits) if (L >> l) & 1) for l in range(N)]
expected_star = [sum(1 << L for L in range(bits)
                     if any((L >> l) & 1 for l in near[p])) for p in range(N)]
strict = [False, False]
for P in range(bits):
    wires = [full_word if (P >> p) & 1 else 0 for p in range(N)] + line_wires
    expected = 0
    for p in range(N):
        if (P >> p) & 1:
            expected |= expected_star[p]
    for op, i, j in gates:
        a, b = wires[i], wires[j]
        wires.append(a & b if op == "and" else a | b)
    assert (wires[out1] & wires[out2]) == expected
    for i, w in enumerate((out1, out2)):
        strict[i] |= bool(wires[w] & ~expected)
assert all(strict)
print(f"{len(gates)} gates ({Counter(op for op, _, _ in gates)}), terminals {out1} and {out2}")
print(f"All {bits * bits:,} input assignments passed; each terminal alone has a false positive.")
