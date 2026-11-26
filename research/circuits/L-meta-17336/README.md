# The missing first-gate case for a nine-input circuit

James Adams (Jamesadams1988) · L-meta-17336

**A counterexample must have exactly 15 gates.** The assigned statement asks for a circuit with fewer than 16 gates for a specified 12-edge function. It also fixes the first gate to NOT of input 5, or AND/OR of input 5 with input 6, 7 or 8. Pinning either input 2 or input 3 to false reduces the function to a published eight-input problem requiring at least 14 gates. Each pin saves a gate, giving the 15-gate lower bound. We have 16-gate constructions beginning with each permitted OR, and 17-gate constructions for all seven choices. Whether 15 suffices is open. [Literal desk statement](centers/statement.json) · [Lower-bound transfers](lower/README.md) · [Lean constructions](upper/README.md)

| Route | Result |
|---|---|
| Restrictions of a 15-gate circuit | Each of inputs 2 and 3 must feed just one effective gate, a binary OR with a computed wire. Six of the seven allowed first gates cannot serve as its other operand. Both reductions and the finite tests passed Lean. The separate rebuild of one upstream donor hit the local memory limit. [Proofs and scope](lower/README.md) |
| First two gates reused freely, with an AND/OR formula afterward | All 700 choices of the first two gates exclude a 15-gate witness. This includes 630 binary second-gate choices and 70 negations. Later shared subcircuits or internal negations in the suffix remain possible. [Certificate and replay](prefixes/README.md) · [Independent formula search](formula/pareto.md) |
| Shared signed disjunctions and individually safe AND products, with arbitrary Boolean postprocessing on products | Exact minima are 16 for each OR-first choice and 17 for each AND-first or NOT-first choice. Exhaustive orientation of the 12 edges gives exactly 20 optimal five-star partitions. [Counting proof and witnesses](centers/README.md) |

## Earlier upstream proof attempt

Grigorescu submitted a proof of the opposite statement in PR #22380. Upstream closed it after two checker timeouts and recorded no verdict on the theorem. Our compiled replay of the numerical parts of that public proof passed all 135 finite assertions. An independent decoder also compared 267 distinct packed assignments with the literal edge function. The replay does not certify the universal soundness argument for arbitrary circuits. [Replay and provenance](prior/README.md) · [Upstream disposition](https://github.com/open-goat/pequalnp-proofs/pull/22380#issuecomment-7179084232)

## Reproduce the results

Use upstream commit `c468e9f20b8fea4dc13ef9abde683cb439979a1c`, Lean 4.36.0, and the pinned Mathlib package cache. Run `bash replay.sh /path/to/pequalnp-proofs/lean` for the Lean constructions, lower-bound transfers, graph comparison and 512-input witness checks. The lower-bound folder documents the two upstream donor proofs; `BUILD_DONOR=1` enables those longer compilations. The prefix, independent formula and prior-candidate searches each have their own replay instructions linked above.
