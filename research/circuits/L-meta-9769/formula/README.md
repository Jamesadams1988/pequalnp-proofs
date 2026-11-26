# The largest induced star forest after deleting one incidence

Deleting one edge from the incidence graph of any projective plane of order four leaves a largest induced star forest of **25 vertices**. Every AND/OR/NOT formula for its edge function must repeat at least **17 distinct input variables** and contain at least **59 input occurrences**. The formula bound allows negation. The proof counts occurrences in a formula tree and does not give the same lower bound for circuits with shared gates.

In the assigned graph, points and lines are each numbered modulo 21. Incidence in the full plane has differences line minus point in {0, 5, 7, 17, 20}. Comparing the 104 listed edges with all 105 full-plane edges finds exactly one deleted incidence, between point 0 and line 0 (input wires 0 and 21).

## An enumeration-free upper bound

Call the punctured graph H and the full incidence graph G. Suppose that H has an induced star forest with at least 26 vertices. Keep exactly 26 of them. Write k for the number on the smaller side. Each side of G has 21 vertices, so 5 ≤ k ≤ 13. The opposite side has 26−k selected vertices and t = k−5 omitted vertices. The argument applies with points and lines exchanged.

The selected subgraph in H is a forest and has at most 25 edges. Restoring the deleted incidence gives at most 26 selected edges in G. For each of the k selected vertices i on the smaller side, let dᵢ be the number of its neighbors among the t omissions in G, and set D = Σdᵢ. All selected vertices have degree five in G, so 5k−D ≤ 26. Any two distinct opposite vertices have a unique common neighbor in G. Counting pairs of omitted neighbors therefore gives

**Σᵢ binom(dᵢ,2) ≤ binom(t,2).**

For 7 ≤ k ≤ 12, use d ≤ 1 + binom(d,2). The two inequalities imply 4k−binom(k−5,2) ≤ 26. The six left sides are 27, 29, 30, 30, 29, and 27. For k = 13, D ≥ 39. Since 2d ≤ 3 + binom(d,2), the pair count must be at least 2D−39 ≥ 39, even though eight omitted vertices admit only 28 pairs.

For k = 5 or 6, at most one opposite vertex is omitted. Every selected vertex on the smaller side consequently has degree at least three in the selected subgraph of H, even allowing for the deleted incidence. In a star forest two such vertices cannot share a selected neighbor. Each of their pairs has a unique common neighbor in G. Each omission accounts for at most binom(5,2) = 10 pairs, and deleting one incidence can destroy the common neighbor of at most four additional pairs. Indeed each such pair must contain the deleted edge's endpoint on the smaller side and one of the other four vertices through its opposite endpoint. Thus binom(k,2) ≤ 10t+4. At k = 5 this gives 10 ≤ 4, and at k = 6 it gives 15 ≤ 14.

For equality, choose all five points on any line and the other twenty lines. Every selected line meets the chosen five points at exactly one point. These 25 vertices induce a star forest in G, and deleting an edge preserves this property.

## Consequence for formulas

Every input of H is essential, since it belongs to at least one edge. Consider the variables occurring exactly once in a formula computing the edge function. If four of them induce a path on four vertices, setting all other inputs to false gives a read-once AND/OR/NOT formula for the path's edge function. Push negations to the leaves and simplify constants. A surviving essential variable occurs positively because the path function is increasing in each variable, while a unique negative occurrence would be decreasing.

A positive read-once formula for this path is impossible. The two root subformulas use disjoint nonempty variable sets. At an OR root all minimal true supports lie wholly inside one of the two sets, but the path is connected. At an AND root the minimal true supports are all unions of one minimal support from each child. They all have size two. Hence every minimal support of either child is a singleton, and essentiality makes the resulting graph complete bipartite across the two sets. The four-vertex path is not complete bipartite.

The subgraph on the singly occurring variables thus contains no induced path on four vertices. Any connected bipartite component with this property is complete bipartite: two nonadjacent vertices on opposite sides would give a shortest path of length at least three and its first four vertices would induce the forbidden path. The plane also has no four-cycle, so these components are stars or isolated vertices. There are at most 25 singly occurring variables among the 42 essential variables. The other 17 or more must each occur at least twice, giving at least 42+17 = 59 input occurrences and at least 58 binary gates in a fan-in-two formula.

## Independent bounded replay

The alternative finite check in `star_bound.cpp` enumerates all 2²¹ subsets on one side. For each chosen subset call an opposite vertex light if it meets at most one selected vertex, and heavy otherwise. In a valid star forest any two chosen heavy neighborhoods are disjoint. If a chosen heavy vertex meets any row incident to a light vertex, drop it and include the adjacent light vertices. At least one distinct light vertex can replace each dropped heavy vertex because a light neighborhood contains at most one row and the removed heavy neighborhoods are disjoint. All light vertices may now be kept.

The retained heavy neighborhoods must lie inside the rows untouched by light vertices and be pairwise disjoint. Sort their candidate sizes. Even the smallest t candidates cannot pack if their total size exceeds the number of rows in the union of the candidates. This relaxation already gives the global upper bound 25. Smaller per-row-size bounds from a full packing search can differ. Replay with a C++20 compiler:

```sh
c++ -O3 -std=c++20 star_bound.cpp -o star_bound
./star_bound | cmp - independent-counts.txt
```

`StarForestArithmetic.lean` checks the numerical contradiction given the three incidence-count hypotheses, including the two inequalities for binomial coefficients. From a checkout of the upstream Lean project with its pinned toolchain, run `lake env lean /path/to/StarForestArithmetic.lean`. The derivation of those hypotheses from plane incidence and the formula argument are the mathematical proofs above.
