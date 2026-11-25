# The twelve one-input restrictions of L-meta-13646

James Adams (Jamesadams1988) computed the exact circuit sizes for each way to fix one input of the six-input function `0xeeeaeaeaeee0e8e0`. **Only fixing input 2 to false leaves a function that requires seven gates.** Every other restriction takes at most six. These counts hold for both unrestricted fan-in-two AND/OR/NOT circuits and monotone AND/OR circuits. [Reproducible calculation](cofactor_profile.py)

| Input fixed | Fixed to false | Fixed to true |
|---|---:|---:|
| x0 | 3 | 4 |
| x1 | 4 | 5 |
| x2 | **7** | 1 |
| x3 | 4 | 6 |
| x4 | 6 | 5 |
| x5 | 6 | 4 |

## How the seven-gate restriction proves eight gates

If an input is essential and fixing it leaves a nonconstant function, a circuit for the original function loses at least one gate on restriction. The Lean theorem `CofactorBound.ofPinnedImage` applies this fact when the restricted function is a known lower-bound example after relabeling inputs. Labels may identify inputs. The proof builds on nicohabets’s gate-elimination and relabeling lemmas, which credit sanchan. [Transfer theorem and application](CofactorBound.lean) · [Gate elimination](https://github.com/open-goat/pequalnp-proofs/pull/9322)

With x2 fixed to false, take the remaining inputs in order (0, 3, 1, 4, 5). The resulting table is `0xeaaac880`, the exact table for which Noptus already proved a seven-gate lower bound in L-meta-8657. The original needs at least eight gates. It attains eight by computing the OR of two expressions, `(x0 OR x1) AND (x2 OR (x3 AND x4))` and `x0 AND (x5 OR (x1 AND x3))`. Lean compares the resulting circuit with all 64 rows. [Noptus’s five-input result](https://github.com/open-goat/pequalnp-proofs/pull/12814) · [Lean certificate](CofactorBound.lean)

The desk assigned the negation of the positive statement L-meta-13645. Before this reproduction, foudress’s proof of that statement had already passed the upstream checker. Danielchin’s separate PR also uses the x2=false restriction. Our proof reuses the merged five-input theorem and our calculation gives the complete table above. [Prior checker result](https://github.com/open-goat/pequalnp-proofs/pull/17698#issuecomment-7171515635) · [Danielchin’s restriction proof](https://github.com/open-goat/pequalnp-proofs/pull/18069) · [Literal assignment](statement.txt)

## Reproduce the counts

Run `python3 cofactor_profile.py` with Python 3.10 or newer. The script prints a monotone formula for each face, with letters a through e naming the surviving inputs in ascending order. It searches every distinct set of wires obtainable in up to four gates, then all useful one- and two-gate continuations. Signals may be shared, NOT gates are allowed, and both constants are free in the lower-bound search. Each lower bound matches the gate count of its displayed formula in the project model. A separate normalized circuit enumeration and a SAT calculation with Lean-checked LRAT certificates independently reproduced all twelve counts.

The script also accepts a six-input truth table as a hexadecimal or decimal argument. Its lower-bound search extends through size six and its monotone formula search through size seven. A lower bound of seven and a missing formula leave the exact size open.

## Replay the project checker

Prepare upstream commit `b0bb9eaa703fa256d5ebc1540bc1d419f160e57c` with its pinned Lean 4.36.0, Mathlib cache and verifier. From this research directory, run the following commands against a clean checkout. The generator verifies the source hashes and creates the diagnostic in a fresh file. Its only import is `PEqualNP.Defs`. [Diagnostic generator](pack_refutation.py) · [Upstream checker](https://github.com/open-goat/pequalnp-proofs/blob/b0bb9eaa703fa256d5ebc1540bc1d419f160e57c/tools/check-lean.mjs)

```sh
research_dir=$PWD
upstream=/path/to/prepared/upstream
proof=lean/PEqualNP/Outside/L_meta_13646.lean
python3 pack_refutation.py "$upstream" "$upstream/$proof" &&
  (cd "$upstream" && node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute)
```

The official local verifier returned `ACCEPTED (refute)` for source SHA-256 `80f8aaa9187860cafabe4cb965bf622dc8c0a452f2555d8e960aab7d2c647b32`. It rechecked 2,173 constants and reported only `propext`, `Quot.sound` and `Classical.choice`.
