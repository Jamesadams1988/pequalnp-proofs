"""Construct a depth-five 16-gate circuit for the graph of L-meta-11021."""
from collections import defaultdict
from itertools import combinations, product
import heapq


EDGES = ((0, 4), (0, 5), (1, 5), (2, 6), (3, 6), (0, 7),
         (2, 7), (4, 7), (1, 8), (3, 8), (4, 8), (6, 8))


def star_circuit(stars):
    gates = []
    depths = [0] * 9

    def gate(op, a, b):
        gates.append((op, a, b))
        depths.append(1 + max(depths[a], depths[b]))
        return len(depths) - 1

    def disjoin(wires):
        pool = [(depths[w], w) for w in wires]
        heapq.heapify(pool)
        while len(pool) > 1:
            _, a = heapq.heappop(pool)
            _, b = heapq.heappop(pool)
            w = gate("or", a, b)
            heapq.heappush(pool, (depths[w], w))
        return pool[0][1]

    terms = [gate("and", center, disjoin(neighbors)) for center, neighbors in sorted(stars.items())]
    output = disjoin(terms)
    return gates, depths[output]


def verify(gates):
    for x in range(512):
        values = [(x >> i) & 1 for i in range(9)]
        target = any(values[a] & values[b] for a, b in EDGES)
        for op, a, b in gates:
            values.append(values[a] & values[b] if op == "and" else values[a] | values[b])
        if values[-1] != target:
            raise ValueError(f"bad circuit at assignment {x}")


def main():
    covers = [s for s in combinations(range(9), 5) if all(a in s or b in s for a,b in EDGES)]
    candidates = []
    for cover in covers:
        for chosen in product(*[[v for v in edge if v in cover] for edge in EDGES]):
            stars = defaultdict(list)
            for (a, b), center in zip(EDGES, chosen):
                stars[center].append(b if a == center else a)
            gates, depth = star_circuit(stars)
            candidates.append((depth, gates))
    depth, gates = min(candidates)
    verify(gates)
    if (len(gates), depth) != (16, 5):
        raise ValueError("expected 16 gates at depth 5")
    print(f"{len(covers)} five-vertex covers, {len(candidates)} center assignments")
    print(f"{len(gates)} gates at depth {depth}, all 512 assignments verified")
    for i, (op, a, b) in enumerate(gates, start=9):
        print(i, op, a, b)
    return gates


if __name__ == "__main__":
    main()
