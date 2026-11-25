# Does a NOT gate save a gate on this seven-input function?

Independent circuit and tests by James Adams (Jamesadams1988).

The function is true when the selected vertices contain an edge of a fixed seven-vertex graph. The question in L-meta-12005 is whether an AND/OR/NOT circuit with at most one NOT can use fewer gates than every AND/OR circuit for that function. Gates take at most two inputs. For this graph the answer is **no**. [Public desk entry](https://pequalnp.com/desk/step?gap=L-meta-12005)

## Exact minimum with unrestricted NOT gates

James Adams's 11-gate AND/OR circuit attains the minimum even when any number of NOT gates is allowed. The proof uses the same seven-input function as the original desk statement. [Lean proof](ExactMinimum.lean) · [Circuit](Witness.lean)

Fix leaf 3 to whichever value saves two gates. In both branches its neighbor 0 is essential. Fixing 0 to false saves another gate and gives the same graph on vertices 1, 2, 4, 5 and 6. Fixing 1 to false saves a fourth gate and leaves a four-clique on 2, 4, 5 and 6. Every unrestricted circuit for that clique needs at least seven gates, giving the matching lower bound of eleven. The lemma `LeafTransfer.threeGateRestriction` packages the first two steps for other functions with the same restriction pattern. [Gate-elimination lemmas from nicohabets, crediting sanchan](https://github.com/open-goat/pequalnp-proofs/pull/9322) · [Four-clique bound by hilelyos](https://github.com/open-goat/pequalnp-proofs/pull/13494)

To replay from this directory, use the project's pinned Lean 4.36.0 with Mathlib and `PEqualNP.Defs` built, then run `bash check_leaf_transfer.sh ../../../lean`. The script checks the source hashes, rebuilds both imported proofs in a temporary directory, and prints the axiom dependencies of the reusable lemma and the exact minimum. [Replay script](check_leaf_transfer.sh)

## A three-gate bound for other graphs

For the Boolean function that detects an edge among selected vertices of a finite simple graph, write `N(p)` for the neighbors of vertex `p`. Suppose `N(p)` is nonempty and is a proper subset of `N(q)`. Given any unrestricted circuit of size at most `s` for this function, the function with `q` fixed to true has a circuit of size at most `s − 3`. In particular, a lower bound of `L` gates for the restricted function gives a lower bound of `L + 3` for the original. James Adams's Lean theorem proves this implication for all finite simple graphs in the project's fan-in-two model. [Lean proof](DominatedGraph.lean)

Once `q` is true, any edge detected through `p` can also be detected through `q`. A neighbor of `q` outside `N(p)` witnesses that changing `q` can change the output for either fixed value of `p`. Strict inclusion matters. In the three-vertex path with endpoints `p` and `q`, the endpoints have the same neighbors, and changing `q` has no effect once `p` is true.

The Lean replay command above also checks this graph theorem. Run `python3 verify_graph_pins.py` for an independent truth-table test of both pin values on all 1,100 labeled simple graphs with zero through five vertices. It compares the graph criteria with the literal hypotheses on 21,300 ordered vertex pairs. [Finite replay and controls](verify_graph_pins.py)

To screen a saved public desk export, run `python3 screen_graph_pins.py /path/to/gaps.json`. Add `--show-hits` to print the vertex pairs. The scanner recognizes flat numeric edge lists, typed pairs and explicit edge disjunctions. It groups by vertex count and labeled edge set. A match identifies a lower-bound proof step. A complete proof still needs a bound for the restricted function, and the desk determines assignment availability. [Scanner](screen_graph_pins.py) · [Desk export](https://data.pequalnp.com/data/desk/gaps.json)

## Upper and lower bounds

The 11-gate circuit in `Witness.lean` uses AND and OR. `witness_correct` proves that it computes the exact function on every input. The separate Python replay also compares its output against the edge list for all 128 inputs.

For the lower bound, fix inputs 1, 2 and 3 to zero in that order. Each restriction removes an essential input at a cost of at least one binary gate in the normalized circuit measure. The remaining vertices 0, 4, 5 and 6 form a four-clique. The checked four-clique bound requires at least seven binary gates, for a total of at least ten. A NOT gate adds at least one more gate. A circuit that uses no NOT is already an AND/OR circuit and can be reused as it stands. The Python replay verifies the finite restriction premises. [Restriction lemma](https://github.com/open-goat/pequalnp-proofs/blob/e125f04d0dc6fed67cee48a1d06692912e167c32/lean/PEqualNP/Outside/L_meta_11627.lean#L1092) · [Four-clique bound](https://github.com/open-goat/pequalnp-proofs/blob/e125f04d0dc6fed67cee48a1d06692912e167c32/lean/PEqualNP/Outside/L_meta_11627.lean#L661)

Our Lean theorem `lower_bound_suffices` takes the lower bound as a hypothesis and proves the negation of the exact assigned statement. For a separate end-to-end local check, we used Julleht's proof of the positive twin L-meta-12004 and applied it to a hypothesized L-meta-12005. Lean 4.36.0 checked the resulting contradiction using only `propext`, `Classical.choice` and `Quot.sound`. The proof was taken from commit `9d664e3f01e4d11ff2f94d8b57d8109dfbdca456`. Julleht's upstream PR was open at the time of the replay. [Positive twin proof](https://github.com/open-goat/pequalnp-proofs/pull/15996) · [Earlier generic bound by k-sandhu](https://github.com/open-goat/pequalnp-proofs/pull/14881)

## Reproduce our witness checks

From this directory run `python3 check_obstruction.py` using the Python standard library. From the repository's prepared `lean/` directory run `lake env lean ../research/circuits/L-meta-12005/Witness.lean`.
