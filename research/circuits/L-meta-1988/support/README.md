# One terminal factor depends on every input

Let the final AND have two monotone operands a and b. The formal theorem assumes only that the AND agrees with the incidence graph on each assignment selecting at most two vertices represented as a pair, allowing repetition. Positive instances are the incident point–line pairs. Every other vertex pair lies below a prescribed negative test of L-meta-1988, so the promise and monotonicity imply this hypothesis.

The accepted singleton sets of a and b define a complete bipartite subgraph. For any singleton accepted by a and any singleton accepted by b, their union is accepted by both, so it must be an incidence edge. Two vertices share at most one neighbor in this graph. Thus one fixed operand accepts at most one singleton. For every vertex v, at least three of its four neighbors w yield a one-input sensitivity witness for this same operand, with value false on {w} and true on {v,w}. In particular, the operand depends on all 26 inputs and has at least 48 of the 52 incidence edges as minimal true assignments.

The Lean theorem `ProjectivePlaneTwoFactors.one_factor_sensitive` proves the at-most-one-singleton and three-witness conclusions. The 48 count follows since the possible singleton touches only four edges. The proof checks the concrete degree and common-neighbor properties by kernel reduction. Its reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Run `lake env lean /absolute/path/to/TwoFactors.lean` from the pinned project's Lean directory. The file only imports Mathlib.

## Formal parts of the 31-gate argument

`SplitCover.lean` defines read-once formulas by allowed supports and disjoint gates. Its checked induction constructs at most 2ʰ factors from an h-level certificate of splits at shared wires. It also proves the Boolean identity for a monotone split. `ConeCount.lean` derives the lower bound on shared wires from the cover capacity, then double-counts outdegree to get the 31-gate bound. The graph argument constructing the split certificate for the project's circuit representation is in the [DAG proof](../read-once/DAG.md). Both files import Mathlib and compile by the same command as `TwoFactors.lean`.
