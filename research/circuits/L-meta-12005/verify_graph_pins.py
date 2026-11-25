#!/usr/bin/env python3
"""Compare graph pin criteria with Boolean truth tables for every labelled graph on 0–5 vertices."""

from itertools import combinations, permutations, product
from math import comb


def truth_table(n, edges):
    return {
        x: any(x[i] and x[j] for i, j in edges)
        for x in product((False, True), repeat=n)
    }


def cofactor_vectors(table, p, q):
    vectors = {(a, b): [] for a, b in product((False, True), repeat=2)}
    # Lexicographic traversal gives the same ordering of free bits in each vector.
    for x, output in table.items():
        vectors[x[p], x[q]].append(output)
    return vectors


def hypotheses(vectors, value):
    common_candidate = vectors[False, value]
    return (
        any(vectors[False, b] != vectors[True, b] for b in (False, True)),
        vectors[False, False] != vectors[False, True],
        vectors[True, False] != vectors[True, True],
        common_candidate == vectors[True, value],
        len(set(common_candidate)) == 2,
    )


def graph_criteria(edges, neighbors, p, q):
    false_pin = (
        neighbors[p] == {q}
        and bool(neighbors[q] - {p})
        and any(p not in edge and q not in edge for edge in edges)
    )
    true_pin = bool(neighbors[p]) and neighbors[p] < neighbors[q]
    return false_pin, true_pin


def check_controls():
    # p essential, q essential at p=0 and p=1, common cofactor, nonconstant.
    cases = [
        ("no surviving edge", 3, [(0, 1), (1, 2)], False, (1, 1, 1, 1, 0)),
        ("matching", 4, [(0, 1), (2, 3)], False, (1, 0, 1, 1, 1)),
        ("extra p-neighbor", 4, [(0, 1), (0, 2), (1, 2), (2, 3)], False, (1, 1, 1, 0, 1)),
        ("equal neighborhoods", 3, [(0, 2), (1, 2)], True, (1, 1, 0, 1, 1)),
    ]
    for name, n, edges, value, expected in cases:
        observed = hypotheses(cofactor_vectors(truth_table(n, edges), 0, 1), value)
        if observed != expected:
            raise AssertionError((name, expected, observed))
        print(f"control {name}, q={int(value)}: {''.join(str(int(bit)) for bit in observed)}")


def scan(n):
    possible_edges = list(combinations(range(n), 2))
    pairs = list(permutations(range(n), 2))
    passing_pairs = [0, 0]
    passing_graphs = [0, 0]
    graphs = pair_count = weak_inclusion_false_positives = 0
    for inclusion in product((False, True), repeat=len(possible_edges)):
        edges = [e for e, present in zip(possible_edges, inclusion) if present]
        neighbors = [set() for _ in range(n)]
        for i, j in edges:
            neighbors[i].add(j)
            neighbors[j].add(i)
        table = truth_table(n, edges)
        has_witness = [False, False]
        graphs += 1
        for p, q in pairs:
            pair_count += 1
            vectors = cofactor_vectors(table, p, q)
            direct = tuple(all(hypotheses(vectors, b)) for b in (False, True))
            structural = graph_criteria(edges, neighbors, p, q)
            if direct != structural:
                raise AssertionError((n, edges, p, q, direct, structural))
            for b, passed in enumerate(direct):
                if passed:
                    passing_pairs[b] += 1
                    has_witness[b] = True
            if neighbors[p] and neighbors[p] <= neighbors[q] and not direct[True]:
                weak_inclusion_false_positives += 1
        for b, passed in enumerate(has_witness):
            passing_graphs[b] += passed

    if graphs != 2 ** comb(n, 2) or pair_count != graphs * n * (n - 1):
        raise AssertionError(("incomplete enumeration", n, graphs, pair_count))
    if n >= 2:
        k = n - 2
        core_graphs = 2 ** comb(k, 2)
        expected_false = len(pairs) * (2**k - 1) * (core_graphs - 1)
        expected_true = len(pairs) * (3**k - 2 * 2**k + 1) * core_graphs
        if passing_pairs != [expected_false, expected_true]:
            raise AssertionError(("count formula", n, passing_pairs, expected_false, expected_true))
    return (graphs, pair_count, *passing_pairs, *passing_graphs, weak_inclusion_false_positives)


def main():
    check_controls()
    print("n graphs ordered_pairs false_pairs true_pairs false_graphs true_graphs weak_false_positives")
    rows = []
    for n in range(6):
        row = scan(n)
        rows.append(row)
        print(n, *row)
    print("all", *(sum(column) for column in zip(*rows)))
    print("All truth-table and structural results agree for both pin values.")


if __name__ == "__main__":
    main()
