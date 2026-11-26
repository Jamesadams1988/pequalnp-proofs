"""Exact weighted biclique cover and circuit replay for the nine-input edge function."""
from functools import lru_cache
from itertools import combinations

EDGES = ((0, 4), (1, 5), (0, 6), (1, 6), (2, 6), (0, 7),
         (3, 7), (4, 7), (2, 8), (3, 8), (5, 8), (7, 8))
EDGE_INDEX = {tuple(sorted(edge)): i for i, edge in enumerate(EDGES)}
VERTICES = tuple(range(9))


def subsets():
    for size in range(1, 10):
        yield from combinations(VERTICES, size)


def bicliques():
    parts = list(subsets())
    for left, right in combinations(parts, 2):
        if set(left).intersection(right):
            continue
        product = [tuple(sorted((a, b))) for a in left for b in right]
        if all(edge in EDGE_INDEX for edge in product):
            yield (sum(1 << EDGE_INDEX[e] for e in product), left, right)


def minimum_cover(rectangles):
    @lru_cache(None)
    def cover(missing):
        if missing == 0:
            return 0, ()
        first_edge = missing & -missing
        candidates = []
        for i, (edges, left, right) in enumerate(rectangles):
            if edges & first_edge:
                cost, witness = cover(missing & ~edges)
                candidates.append((cost + len(left) + len(right), (i,) + witness))
        return min(candidates)

    return cover((1 << len(EDGES)) - 1)


def make_circuit(rectangles, witness):
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return len(VERTICES) + len(gates) - 1

    def disjoin(wires):
        current, *rest = wires
        for other in rest:
            current = gate("OR", current, other)
        return current

    products = []
    for i in witness:
        _, left, right = rectangles[i]
        products.append(gate("AND", disjoin(left), disjoin(right)))
    output = disjoin(products)
    return gates, output


def replay(gates, output):
    for mask in range(512):
        values = [(mask >> i) & 1 for i in VERTICES]
        target = any(values[a] & values[b] for a, b in EDGES)
        for op, a, b in gates:
            values.append(values[a] & values[b] if op == "AND" else values[a] | values[b])
        if values[output] != target:
            raise ValueError(f"truth-table mismatch at assignment {mask}")


def main():
    rectangles = list(bicliques())
    four_cycles = sum(len(left) == len(right) == 2 for _, left, right in rectangles)
    covers = [part for part in subsets() if all(a in part or b in part for a, b in EDGES)]
    min_centers = min(map(len, covers))
    cost, witness = minimum_cover(rectangles)
    gates, output = make_circuit(rectangles, witness)
    replay(gates, output)
    if (len(rectangles), four_cycles, min_centers, cost, len(gates)) != (47, 0, 5, 17, 16):
        raise ValueError("enumeration disagrees with the recorded graph")
    print(f"{len(rectangles)} nonempty bicliques, {four_cycles} four-cycles")
    print(f"Minimum vertex cover size {min_centers} "
          f"({sum(len(c) == min_centers for c in covers)} distinct minimum covers)")
    print(f"Minimum sum of side cardinalities {cost}")
    for i in witness:
        _, left, right = rectangles[i]
        print(f"  {left} x {right}")
    print(f"{len(gates)} gates, verified on all 512 inputs")
    for i, (op, a, b) in enumerate(gates, start=9):
        print(f"  {i} = {op} {a} {b}")


if __name__ == "__main__":
    main()
