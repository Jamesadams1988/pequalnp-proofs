# Biclique-cover optimum for L-meta-11031

The minimum circuit size is 16 within the following construction. Take a cover of the graph edges by complete bipartite subgraphs. For each subgraph with sides A and B, compute the OR of each side, then AND the two values. Finally OR the product terms. Each OR tree and product term is built independently. Overlap between covered edge sets is allowed.

A term costs |A| + |B| − 1 binary gates. Joining the terms with OR gives total size equal to the sum of the side cardinalities minus one. The checker enumerates every nonempty biclique from disjoint vertex subsets. For each set of uncovered edges it selects one edge, tries every biclique containing it, and minimizes the side-cardinality cost plus the cost of the remaining edges. Each recursive call removes at least the selected edge.

All 47 bicliques of this graph are stars. The result can also be checked by counting centers. Covering the 12 edges needs at least five stars, because the center set must be a vertex cover and every vertex cover has size at least five. The sum of the side cardinalities is therefore at least 12 + 5 = 17. The recorded circuit achieves this sum by partitioning the edges among five stars, and the checker evaluates its 16 gates on all 512 inputs.

Run `python3 -B verify.py` and compare the output with `expected.txt`. The restricted optimum applies to the construction above. The explicit circuit also supplies an unrestricted upper bound.
