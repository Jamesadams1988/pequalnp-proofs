# Independent audit of the cofactor bound

Run `python3 -B small_audit.py` with a C++20 compiler on PATH. The script compiles `bound.cpp` in a temporary directory, compares its recurrence against a direct implementation, and checks its lower bounds against exhaustive monotone circuit synthesis. Supply `--solver PATH` to reuse an executable. Add `--full` to reproduce the assigned graph's root output and independently count its nonempty isolate-free masks.

## Recurrence checks

Removing isolated vertices preserves the exact optimal size. An old circuit can be restricted by pinning such inputs to zero, and a circuit on the remaining inputs can be relabeled to ignore them. An edgeless graph has cost zero under the project's default-false output convention. The only nonempty isolate-free graph with two vertices is one edge, with exact cost one. For a core on n vertices every vertex is essential, witnessed by a neighboring singleton and its extension to their edge. The output cone of a binary circuit therefore contains at least n−1 gates by counting its input and gate nodes and at most two incoming arcs per gate.

Pin an essential variable v. At least one useful gate reads that variable. Substituting a constant for v eliminates such a gate by absorption or identity. Propagating constants and copies forward introduces no gates. Both cofactors of a graph edge function are false when all remaining bits are zero, so a constant result can use default false. Pinning v to zero leaves the induced graph on the other vertices. Pinning it to one yields the OR of its d neighbors as unit inputs and the edge function of the graph obtained by removing v and those neighbors. Edges touching a unit are absorbed. If the residual has an edge, pinning those units to zero successively costs at least one gate per unit, since the current function still depends on both that unit and the residual. Thus the high cofactor requires at least d plus the residual lower bound. With no residual edge, the high function is the OR of d distinct variables and has exact cost d−1.

Before choosing a first gate, restrict to the active vertices and trim the output cone. Constant, unary, repeated-input, and invalid first reads simplify by the same identities. A minimum circuit for the nontrivial core therefore starts with AND or OR on two distinct raw inputs. Once n exceeds two, that first gate cannot be the output, so it has a useful consumer. Neutral pinning removes the first gate. Absorbing pinning also simplifies at least one consumer since a constant now occupies one of its inputs. This gives the stated two-gate saving for the absorbing branch regardless of fan-out, including when both consumer inputs become constants. Both endpoints of the first gate give constraints, so a proposed pair pays the larger of its two vertex scores. Minimizing over all distinct pairs gives the second smallest score, counting equal scores with multiplicity. The unknown operation permits taking the smaller of the AND and OR floors.

## Independent finite checks

The reference recurses on actual immutable sets of edges. It enumerates both endpoints of every candidate first gate and every induced vertex set when checking the small graphs. It compares all reported fields, including the omission of separate root floors when the root has an isolated vertex or at most two active vertices.

The exact synthesis enumerates DAGs breadth-first as sets of available five-variable truth tables. Each transition adds the AND or OR of two available signals. Either may be reused later. Commutativity permits unordered operand pairs. Duplicate signals and constants can be removed from a minimum circuit for a nonconstant target. The empty target is assigned its native zero-gate realization. A fixed left or right input unused by a smaller graph does not reduce its optimum, since it can be pinned to zero. The search reached every labeled 2-by-3 graph within five gates.

| Exact gate count | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| Labeled 2-by-3 graphs | 1 | 6 | 9 | 11 | 19 | 18 |

Across all 98 labeled graphs with one or two left vertices and one, two or three right vertices, the C++ and reference recurrences agreed. The recurrence matched the exact size in 64 cases and fell short by one in the other 34.

For the full graph, fix a nonempty left subset A. To obtain a core the selected right vertices must lie inside its neighborhood N(A) and meet the neighborhood of every chosen left vertex. Inclusion-exclusion over subsets T of A counts such choices by summing (−1)^|T| · 2^|N(A) ∖ N(T)|. Summing over A uses 3¹³−1 signed terms and independently yields **30,185,957 nonempty isolate-free masks**. The C++ full replay gives 29 for all three root floors and for the resulting lower bound. Numerical agreement with exact circuit synthesis concerns the small graphs above.
