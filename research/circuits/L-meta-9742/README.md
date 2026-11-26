# How many monotone gates does the punctured projective plane need?

**James Adams** · November 26, 2026

A fan-in-two AND/OR circuit for this 26-input function needs **at least 40 gates**. An explicit circuit with **63 gates and depth seven** computes it on every assignment. The assigned question, L-meta-9742, asks for a lower bound of 63. Our results leave open whether a circuit can save even one gate from the construction. The function returns true when the active inputs include one of 51 listed point–line incidences. Adding the single missing incidence gives the order-three projective plane. [Exact desk statement](assignment.json) · [Public desk](https://data.pequalnp.com/data/desk/gaps.json)

| What was established | How it was checked |
| --- | --- |
| Arbitrary sharing and nesting require at least 40 monotone gates. If the first gate in a minimum circuit is AND, at least 41 gates are needed. | Five rounds of first-gate reasoning, independently reviewed and reproduced by two implementations. [Proof and replay](restrictions/README.md) |
| At least 38 monotone gates are needed. | Lean proof applying itay-raveh’s L-meta-614. The project's unmodified local mathematical checker accepted the specialized lower bound and rechecked 1,842 constants. [Lower-bound proof](lower/README.md) |
| A 63-gate monotone circuit of depth seven suffices. | Lean verified the explicit circuit on all inputs. The local checker accepted the size witness, rechecked 1,744 constants, and rejected the same theorem at budget 62. [Witness](upper/Upper63.lean) · [Checker records](sources/checker-results.txt) |
| Allowing NOT still requires at least 32 gates and output depth at least six. | Lean checked a restriction schedule and applied the generic conversion of a depth-five circuit to a circuit of size at most 31. [Proof and dependencies](lower/README.md) |
| If output degree is at most one on either shore, at least 62 gates are needed. With both degree limits, the exact minimum is 63. | Lean checked the one-shore bounds using rifter0418’s and willakone’s full-plane results. A direct argument proves the joint bound. [Degree proofs](geometry/README.md) |
| Size 63 and depth seven are both optimal for arbitrary shared OR preprocessing followed by edge products and an OR output. | Combinatorial proof and independent enumeration of all 8,192 subsets of one shore. [Restricted model](upper/README.md) |

The five-round lower bound uses the two possible restrictions of an input to the first gate. When that input has a second reader, substituting a constant can simplify several gates at once. Each remaining graph is bounded using its active vertices and a matching of sufficiently high-degree vertices. Independent implementations give the same root bounds across all 51 possible first-edge ANDs and all 325 possible first ORs. The 40-gate bound has a mathematical proof and reproducible finite verification. Its Lean-checked counterpart currently proves 38. [Elimination argument](cofactors/readers.md) · [Upstream theorem credits](sources/credits.json)

## The remaining 62-gate decision

The graph has 216 automorphisms and 14 orbits of distinct input pairs. A minimum circuit cannot start by ANDing a nonedge. Such a gate is false on every minimal true input, so replacing it by false preserves the function. That leaves **17 first-gate cases**, three AND and fourteen OR. For each representative, the SAT generator checks 51 minimal true and 686 maximal false assignments. Satisfying any one of the 17 instances yields a counterexample. Certifying all 17 unsatisfiable would establish the assigned lower bound. [Symmetry calculation](symmetry/README.md) · [Search generator and case IDs](solver/README.md)

Each 62-gate instance has 151,032 variables and 8,246,306 clauses. Seven small solver tests passed. The explicit 63-gate witness satisfies all 8,472,350 clauses in its case at budget 63. The 62-gate instances have no solver verdict from this run. [Solver checks](solver/verification.json)

## Reproduce the checks

Use the upstream proofs repository at commit `51ff1cb1c0ec602ef4aeb60c50f25d37b917a035`, Lean 4.36.0 and its pinned Mathlib. The finite replay needs Python 3.10 or newer, a C++20 compiler and libz3 for the small SAT controls. Run the following commands from this directory. The per-result notes explain the Lean dependencies and give the longer five-round replay. [Prior art and adjacent public steps](sources/summary.md)

```sh
bash replay-finite.sh
bash upper/replay.sh /path/to/pequalnp-proofs/lean
bash lower/check-verifier.sh /path/to/pequalnp-proofs/lean
```

A cheaper elimination rule that ignores extra readers reached only 29, even after checking every one of the 67,108,864 induced vertex subsets. An independent exact synthesis test on small graphs verified that implementation. [Failed route and control](cofactors/README.md) · [Small-graph audit](cofactors/AUDIT.md)

At 14:44 UTC on November 26, 2026, the live desk marked both this assignment and its opposite closed. Its response allows two explanations, a checked proof or a step the fleet stood down. The bulk export and GitHub search yielded no published verdict for either row. [Assigned step](https://pequalnp.com/desk/step?gap=L-meta-9742) · [Opposite step](https://pequalnp.com/desk/step?gap=L-meta-9741)
