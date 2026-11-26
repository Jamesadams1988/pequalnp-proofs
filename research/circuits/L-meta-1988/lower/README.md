# Lower bounds for the promised virtual AND

The promised virtual output requires at least **30 gates in the supplied circuit**. Appending its AND as one gate gives an ordinary circuit for the 52-edge predicate. Lean proves that every fan-in-two AND/OR/NOT circuit for that predicate uses at least 31 gates. Both bounds allow unrestricted reuse of gate outputs. The open desk bound is 63 for the supplied circuit.

[Lower.lean](Lower.lean) specializes the semantic argument from the upstream reduction R-meta-1988-2. On any assignment containing an incident pair, monotonicity propagates the positive singleton test. On an edge-free assignment, at least one shore has size at most three. If four points are chosen, at most three lines avoid them, by the accepted L-meta-6528 theorem. Monotonicity therefore places every edge-free assignment below a tested negative assignment. The proof accounts for default-false wire reads and arbitrary output lists of length at most two. Its final theorem repeats the assigned proposition with 30 in place of 63. [Upstream reduction](https://github.com/open-goat/pequalnp-proofs/blob/cca62ead6f33b7b15e65024b50f58515ceb1ba75/lean/PEqualNP/Outside/R_meta_1988_2.lean) · [Geometry theorem](https://github.com/open-goat/pequalnp-proofs/blob/cca62ead6f33b7b15e65024b50f58515ceb1ba75/lean/PEqualNP/Outside/L_meta_6528.lean)

[Elimination.lean](Elimination.lean) adapts the fork’s earlier L-meta-9769 gate-elimination certificate. Of 16 successive pins, six allow Lean’s elimination lemma to choose either input value, saving two gates each. The other ten fix the input to false and save one gate each. Ten variables remain essential on every resulting branch, requiring another nine gates. The circuit-size bound is therefore 12 + 10 + 9 = 31.

[Degrees.lean](Degrees.lean) proves a separate obstruction. If the supplied circuit has size at most 62, the appended circuit’s output has syntactic degree at least two on the point inputs and at least two on the line inputs. The output wire is the explicit AND of the designated wires. For each shore, the proof relabels the input wires and applies L-meta-1500. It uses the rewiring and degree-preservation lemmas of L-meta-4580. [Line-degree obstruction](https://github.com/open-goat/pequalnp-proofs/blob/cca62ead6f33b7b15e65024b50f58515ceb1ba75/lean/PEqualNP/Outside/L_meta_1500.lean) · [Rewiring lemmas](https://github.com/open-goat/pequalnp-proofs/blob/cca62ead6f33b7b15e65024b50f58515ceb1ba75/lean/PEqualNP/Outside/L_meta_4580.lean)

Use Lean 4.36.0 and a project checkout with these modules built. Build the prerequisites from the project’s Lean directory.

```sh
lake build +PEqualNP.MetaComplexity.Helpers.PermInputs +PEqualNP.Outside.L_meta_6528 +PEqualNP.Outside.L_meta_1500 +PEqualNP.Outside.L_meta_4580
```

Run `./replay.sh /path/to/pequalnp-proofs/lean` from this folder to compile all three local modules.
