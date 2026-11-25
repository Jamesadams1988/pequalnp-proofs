"""Check the restriction chain and the literal Lean circuit on every input."""
from itertools import combinations
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROWS = range(256)


def read_graph():
    statement = (HERE / "statement.txt").read_text()
    lists = re.findall(r"\[([\d, ]+)\] : List ℕ", statement)
    assert len(lists) == 6 and len(set(lists)) == 1
    labels = [int(x) for x in lists[0].split(",")]
    edges = set(zip(labels[::2], labels[1::2], strict=True))
    assert len(edges) == 11 and all(0 <= a < b < 8 for a, b in edges)
    return edges


def pin(table, vertex, value):
    return [table[(row & ~(1 << vertex)) | (value << vertex)] for row in ROWS]


def essential_pairs(table, vertex):
    return sum(table[row] != table[row ^ (1 << vertex)] for row in ROWS) // 2


def check_pins(table):
    after_twin = pin(table, 2, False)
    clique = (0, 4, 6, 7)
    for value in (False, True):
        after_leaf = pin(after_twin, 5, value)
        after_neighbor = pin(after_leaf, 1, False)
        after_last = pin(after_neighbor, 3, False)
        chain = ((table, 2), (after_twin, 5), (after_leaf, 1), (after_neighbor, 3))
        counts = [essential_pairs(t, v) for t, v in chain]
        assert all(counts)
        for restricted in (after_twin, after_leaf, after_neighbor, after_last):
            assert not restricted[0] and restricted[(1 << 0) | (1 << 4)]
        assert all(after_last[row] == (sum((row >> i) & 1 for i in clique) >= 2)
                   for row in ROWS)
        print(f"Pin 5 to {int(value)}: essential-pair counts {counts}. K4 matches all 256 inputs.")


def check_witness(table, edges):
    source = (HERE / "ExactMinimum.lean").read_text()
    witness = source.split("def monoWitness : Circuit :=", 1)[1].split("theorem witness_ops", 1)[0]
    gates = [(op, int(a), int(b)) for op, a, b in re.findall(
        r"⟨\.(and|or), \[(\d+), (\d+)\]⟩", witness)]
    output = int(re.search(r"\], (\d+)⟩", witness)[1])
    assert len(gates) == 12 and 0 <= output < 8 + len(gates)
    assert all(max(a, b) < 8 + i for i, (_, a, b) in enumerate(gates))
    for row in ROWS:
        wires = [(row >> i) & 1 for i in range(8)]
        for op, a, b in gates:
            wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
        assert wires[output] == table[row]
    assert all(table[(1 << a) | (1 << b)] == ((a, b) in edges)
               for a, b in combinations(range(8), 2))
    print(f"Wire {output} matches all 256 inputs, including all 28 vertex pairs.")


if __name__ == "__main__":
    edges = read_graph()
    table = [any((row >> a) & (row >> b) & 1 for a, b in edges) for row in ROWS]
    check_pins(table)
    check_witness(table, edges)
