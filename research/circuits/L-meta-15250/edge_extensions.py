"""Enumerate fresh-input extensions of the two-operand gates in L-meta-8650.

Each edit inserts one gate directly before its consumer. The other consumers
of the same source keep their original wires. Standard-library Python 3.9+.
"""

from collections import defaultdict

# The original circuit's five inputs occupy wires 0..4, gates occupy 5..11.
BASE = (
    ("or", 1, 2), ("and", 0, 4), ("and", 1, 2), ("or", 6, 7),
    ("and", 0, 5), ("or", 3, 9), ("and", 8, 10),
)
BASE_TABLE = 0xEAA8C080
ASSIGNED = (3936927872 << 32) + 3934830720
MASK32 = (1 << 32) - 1


def insert(gate, operand, op):
    """Construct a netlist with six inputs, inserting op(old_operand, x5)."""
    wires = list(range(5))
    net = []
    for j, (kind, a, b) in enumerate(BASE):
        inputs = [wires[a], wires[b]]
        if j == gate:
            net.append((op, inputs[operand], 5))
            inputs[operand] = 5 + len(net)
        net.append((kind, *inputs))
        wires.append(5 + len(net))
    return net


def truth(n, net):
    table = 0
    for row in range(1 << n):
        wires = [(row >> i) & 1 for i in range(n)]
        for op, a, b in net:
            if op == "and":
                wires.append(wires[a] & wires[b])
            elif op == "or":
                wires.append(wires[a] | wires[b])
            else:
                raise ValueError(op)
        table |= wires[-1] << row
    return table


def main():
    assert truth(5, BASE) == BASE_TABLE
    edits = defaultdict(list)
    for gate, (_, a, b) in enumerate(BASE):
        for operand, old_wire in enumerate((a, b)):
            for op in ("and", "or"):
                circuit = insert(gate, operand, op)
                assert len(circuit) == 8
                table = truth(6, circuit)
                low, high = table & MASK32, table >> 32
                assert (high if op == "and" else low) == BASE_TABLE
                edits[table].append((gate, operand, old_wire, op))
    essential = {t for t in edits if (t >> 32) != (t & MASK32)}
    print(f"{sum(map(len, edits.values()))} edits, {len(edits)} distinct tables, "
          f"{len(essential)} distinct with essential x5")
    print(f"{sum(len(edits[t]) for t in essential)} edits have essential x5")
    print(f"Matching edits for the assigned table: {len(edits[ASSIGNED])}")
    assert sum(map(len, edits.values())) == 28
    assert len(edits) == len(essential) == 15
    assert edits[ASSIGNED] == [(0, 1, 2, "and")]
    for gate, operand, old_wire, op in edits[ASSIGNED]:
        print(f"base gate {gate}, operand {operand}, source wire {old_wire}, "
              f"inserted {op} with x5 (zero-based indices)")


if __name__ == "__main__":
    main()
