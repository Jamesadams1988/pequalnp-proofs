"""Replay the finite premises for applying upstream L_meta_11627's lower bound."""

from itertools import combinations


EDGES = ((0, 3), (0, 4), (1, 4), (2, 4), (0, 5), (1, 5), (2, 5),
         (4, 5), (0, 6), (1, 6), (2, 6), (4, 6), (5, 6))
GATES = (("or", 4, 5), ("and", 4, 5), ("or", 7, 6), ("and", 7, 6),
         ("or", 10, 8), ("or", 0, 1), ("or", 12, 2), ("and", 13, 9),
         ("or", 11, 14), ("and", 0, 3), ("or", 15, 16))


def edge_function(bits):
    return any(bits & (1 << i) and bits & (1 << j) for i, j in EDGES)


def witness(bits):
    wires = [bool(bits & (1 << i)) for i in range(7)]
    for op, i, j in GATES:
        assert i < len(wires) and j < len(wires)
        assert op in ("and", "or")
        wires.append(wires[i] and wires[j] if op == "and" else wires[i] or wires[j])
    return wires[-1]


def main():
    assert len(GATES) == 11
    assert all(witness(x) == edge_function(x) for x in range(128))
    print("11-gate monotone witness agrees with all 128 assignments")

    # remove_var needs a changed assignment and a nonzero residual function at each step.
    alive = 127
    for variable, neighbor in [(1, 4), (2, 4), (3, 0)]:
        pair = (1 << variable) | (1 << neighbor)
        assert edge_function(pair & alive)
        alive &= ~(1 << variable)
        assert not edge_function(pair & alive)
        assert edge_function(((1 << 4) | (1 << 5)) & alive)
    clique = [i for i in range(7) if alive & (1 << i)]
    assert clique == [0, 4, 5, 6]
    assert all(not edge_function(1 << i) for i in clique)
    assert all(edge_function((1 << i) | (1 << j)) for i, j in combinations(clique, 2))
    print("All three essential-variable restrictions retain a nonzero function")
    print("Four surviving vertices reject all four singletons and accept all six pairs")


if __name__ == "__main__":
    main()
