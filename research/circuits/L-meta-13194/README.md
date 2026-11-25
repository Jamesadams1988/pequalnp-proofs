# Nine gates for L-meta-13194

James Adams (Jamesadams1988) independently reproduced the exact gate count for the six-input truth table `0xfffefeeafefefeea`. Both unrestricted circuits and monotone AND/OR circuits need **nine gates** in the project's fan-in-two model. The desk assigned the negation of the assertion that monotone circuits can always match the size bound for this table. The theorem `assignedStatementFalse` refutes that literal assignment. k-sandhu had already proved the positive twin L-meta-13193 by the same two restrictions, and the upstream checker accepted that proof before this reproduction. [Exact Lean proof](ExactMinimum.lean) · [Literal desk statement](statement.txt) · [k-sandhu's upstream verdict](https://github.com/open-goat/pequalnp-proofs/pull/17744#issuecomment-7171591238)

The upper bound is the OR of four terms. They are `x0`, `x1 AND x2`, `(x1 OR x2) AND (x3 OR x4)`, and `(x3 AND x4) AND x5`. Each gate has two inputs. For the lower bound, fix input 0 to false, then input 5 to true. Each input is essential when fixed and each resulting function is nonconstant, so each restriction saves at least one gate. The remaining function tests whether at least two of inputs 1 through 4 are true. Its unrestricted lower bound is seven, giving nine for the original table. The Lean proof uses the elimination lemma from nicohabets, crediting sanchan, and the four-input bound from hilelyos. [Elimination lemma](https://github.com/open-goat/pequalnp-proofs/pull/9322) · [Four-input lower bound](https://github.com/open-goat/pequalnp-proofs/pull/13494)

## Replay and reuse

Run `python3 verify.py` from this directory. The replay checks all 64 circuit outputs and independently rules out every unrestricted circuit of up to six gates for the four-input function, even with free constants. A known three-gate circuit serves as a control for the search. [Python checker](verify.py)

For another six-input truth table, import `two_pin_k4_certificates(table)` from [verify.py](verify.py). Bit `r` is the output on the assignment encoded by integer `r`, with input 0 as its least significant bit. The function returns all ordered pairs of essential input restrictions that leave the four-input threshold. This table produces exactly two orders for the same assignments, `x0=0` and `x5=1`. A control that already computes the threshold and ignores the other two inputs yields no certificate. An empty result leaves the gate minimum open.

To replay the official checker, prepare upstream commit `d26d756bd27648ae82c58181f4924acd87606780` with its pinned Lean 4.36.0, Mathlib cache and verifier. Run the commands below from this research directory. The generator checks the upstream helper hashes and creates a fresh Lean file with the sole import `PEqualNP.Defs`. [Generator](../L-meta-14503/pack_refutation.py) · [Upstream checker](https://github.com/open-goat/pequalnp-proofs/blob/d26d756bd27648ae82c58181f4924acd87606780/tools/check-lean.mjs)

```sh
research_dir=$PWD
upstream=/path/to/prepared/upstream
proof=lean/PEqualNP/Outside/L_meta_13194.lean
python3 ../L-meta-14503/pack_refutation.py --gap 13194 "$upstream" "$upstream/$proof" &&
  (cd "$upstream" && node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute)
```

The official local run returned `ACCEPTED (refute)` for SHA-256 `3dc58286a2474fe5f69873e73e12a428b27be4ef85846aabaf9cc23aef010c92`. It rechecked 2,322 constants and reported only `propext`, `Quot.sound` and `Classical.choice`.
