# One filtered rectangle in the 95-edge incidence graph

Research by **James Adams** on L-meta-9802. The 20 points and 20 lines use separate zero-based indices in `edges.json`. The posted 40-input numbering adds 20 to each line index.

A single filtered rectangle cannot improve the 114-gate direct-star construction, even if the marking disjunction and its final AND are already available at zero cost. This result allows reuse of the raw rectangle by several filters whose outputs are ORed together. It assumes the remaining edges are computed by direct stars, with the input disjunctions for the raw rectangle charged once. It leaves open sharing those input disjunctions with unrelated subcircuits and filtering a rectangle through a more general downstream circuit.

Let `A` be a nonempty set of points, `B` a nonempty set of lines, and `D` any set of positive input literals. On a point-line pair, the gate `(∨A) ∧ (∨B) ∧ (∨D)` accepts the union of `(A ∩ D) × B` and `A × (B ∩ D)`. If either rectangle contains a nonedge, the whole output OR is incorrect on that pair. Removing the marks in `D ∖ (A ∪ B)` preserves all covered edge pairs. These removed marks can create extra accepting triples, but cannot help cover any minimal true input. If the original OR of terms computes the edge function, the reduced OR still accepts every edge pair and only loses accepting inputs, hence remains correct by monotonicity. Several OR-combined filters of the same raw rectangle amount to the union of their marking sets.

When both sides have size at least two, the absence of four-cycles allows at most one marked point and one marked line. A term marking both is a double star centered at adjacent vertices `u, v`. The Boolean identity in `doubleStar` proves this description on every input. Its covered edges number `e = |A| + |B| − 1`. Building the two positive disjunctions and their shared AND costs exactly `e` gates before any filtering. A one-sided term covers a single star with at most this many edges. When either side has size one the same single-star bound applies.

Every edge in this particular graph belongs to a perfect matching. Five explicit permutations cover all 95 edges. For a double star choose a matching containing its central edge. The other 19 matching edges survive deletion of the entire double star. For a single star any perfect matching loses at most one edge. Thus the remaining edges require at least 19 star centers. If `r` edges remain and a cover uses `t` centers, computing the direct stars costs at least `r + t − 1` gates including their output ORs. Each group of `d` edges needs `d − 1` leaf ORs and one center AND. Combining the grouped rectangle with the remaining result adds one more OR. The full cost is at least `e + r + 19 = 114`.

`FilterObstruction.lean` kernel-checks the exact graph, its four-cycle exclusion, the edge-covering matching family, the two-center Boolean identity, the residual 19-center lower bound, the size of a double star, and the arithmetic cost conclusion. `check_filters.py` enumerates every two-sided overbroad rectangle by choosing its central edge and nonempty subsets of the two opposite neighborhoods. It computes the residual minimum cover size by maximum bipartite matching. With the marking and filter both free, 2,435 of the 16,895 choices cost 114 gates, and 14,460 cost 115. Requiring an actual AND and a fresh two-literal marking OR adds two gates to these costs.

## Replay

From this directory, the first command replays both the Python enumeration and the Lean proof. It takes the `lean/` directory of the pinned upstream checkout and uses its toolchain and Mathlib cache. The second command runs just the enumeration with Python 3. [Pinned upstream source](https://github.com/open-goat/pequalnp-proofs/tree/0db966b0f50c36b7a95a561a869db13c8120ca5c)

```sh
./replay.sh /path/to/pequalnp-proofs/lean
python3 check_filters.py
```
