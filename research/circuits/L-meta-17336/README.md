# Exact first-gate results for a nine-input circuit

James Adams (Jamesadams1988) · L-meta-17336

**The three OR-first minima are exactly 16 gates.** Upstream accepted tmuniz1901-code’s proof of L-meta-17335 and withdrew L-meta-17336, the request for a counterexample with at most 15 gates. The lower bound holds for each of the seven prescribed first gates. James Adams’s circuits attain it for `x5 OR x6`, `x5 OR x7` and `x5 OR x8`. The other four choices have certified lower bound 16 and upper bound 17. [Accepted verdict](https://github.com/open-goat/pequalnp-proofs/pull/22678#issuecomment-7179688428) · [Proof and replay](resolution/README.md) · [Lean constructions](upper/README.md)

The earlier fork research used restrictions of inputs 2 and 3 to bound a prospective counterexample below by 15 gates and developed the model-specific results in the table. The accepted lower bound supersedes that unrestricted bound. [Original assignment](centers/statement.json) · [Restriction proofs](lower/README.md)

| Route | Result |
|---|---|
| Restrictions of a 15-gate circuit | Each of inputs 2 and 3 must feed just one effective gate, a binary OR with a computed wire. Six of the seven allowed first gates cannot serve as its other operand. Both reductions and the finite tests passed Lean. The separate rebuild of one upstream donor hit the local memory limit. [Proofs and scope](lower/README.md) |
| First two gates reused freely, with an AND/OR formula afterward | All 700 choices of the first two gates exclude a 15-gate witness. This includes 630 binary second-gate choices and 70 negations. Later shared subcircuits or internal negations in the suffix remain possible. [Certificate and replay](prefixes/README.md) · [Independent formula search](formula/pareto.md) |
| Shared signed disjunctions and individually safe AND products, with arbitrary Boolean postprocessing on products | Exact minima are 16 for each OR-first choice and 17 for each AND-first or NOT-first choice. Exhaustive orientation of the 12 edges gives exactly 20 optimal five-star partitions. [Counting proof and witnesses](centers/README.md) |

## Earlier upstream proof attempt

Grigorescu submitted a proof of the opposite statement in PR #22380. Upstream closed it after two checker timeouts and recorded no verdict on the theorem. Our compiled replay of the numerical parts of that public proof passed all 135 finite assertions. An independent decoder also compared 267 distinct packed assignments with the literal edge function. The replay does not certify the universal soundness argument for arbitrary circuits. [Replay and provenance](prior/README.md) · [Upstream disposition](https://github.com/open-goat/pequalnp-proofs/pull/22380#issuecomment-7179084232)

## Reproduce the results

Use upstream commit `c468e9f20b8fea4dc13ef9abde683cb439979a1c`, Lean 4.36.0, and the pinned Mathlib package cache. Run `bash replay.sh /path/to/pequalnp-proofs/lean` for the Lean constructions, lower-bound transfers, graph comparison and 512-input witness checks. The lower-bound folder documents the two upstream donor proofs; `BUILD_DONOR=1` enables those longer compilations. The prefix, independent formula and prior-candidate searches each have their own replay instructions linked above.
