# Adaptive gate-elimination certificates

The residual function is the OR of a set `U` of individual inputs and the edge function of a graph on a disjoint set `S`. A certificate node proves a lower bound of `|U| + k` gates for every such unit set. It therefore keys the node only by the remaining graph and `k`.

At a leaf every vertex of `S` has a neighbor in `S`, so every input of `U ∪ S` is essential. This proves `|U| + |S| − 1` gates. At an internal node, fixing an endpoint `v` to zero deletes that endpoint and its incident edges. Fixing `v` to one makes all its `d` current neighbors individual unit inputs. Their other incident edges can be dropped, since each such edge implies one of the new units. Vertices that become isolated can be dropped in either branch. Both child graphs contain an edge, so both restricted functions are nonconstant. The project's unrestricted two-gate elimination theorem gives a saving of two gates in one branch. A zero-child guarantee of `k − 2` and a one-child guarantee of `k − 2 − d` therefore prove `k` at the parent. `Adaptive.lean` proves these cofactor identities and the two inference rules for arbitrary finite simple graphs in the project's `HasCircuitSize` model.

Each line of `cert-51.txt` gives two 21-bit masks for the ordinary point and line vertices, a residual goal and a pivot wire. The root starts with all 42 vertices and no individual unit inputs. `find.cpp` reproduced the 1,016 internal states in the certificate. The independent Python checker substitutes every path assignment into all 104 original terms, verifies low and high Boolean assignments witnessing dependence, and checks both children. It checks 1,024 leaves at depth ten. From this directory, run:

```sh
python3 check.py cert-51.txt --claim 51 --assignment ../statement.json
```

`Adaptive.lean` proves the soundness of the branching rule, and `Graph.lean` identifies the graph with the literal target. `Cert46.lean` is a small end-to-end Lean control for this rule. A separate compact Lean proof establishes 51 using fixed and variable pin choices. [51-gate theorem](../lower/Terminal51.lean)

The standard replay also expands the 46-gate certificate from its manifest and checks the generated Lean proof. To expand the larger 51-gate manifest into 2,017 Lean lemmas locally, use `EXPAND_51=1 bash replay.sh /path/to/pequalnp-proofs/lean` from the package root.

For the 51-gate adaptive tree the Python path replay completed. The optional 2,017-lemma Lean expansion reached the run time limit before producing a proof object. The compact 51-gate proof linked above completed independently.
