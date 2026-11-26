# How many gates does a two-wire incidence test need?

**James Adams** · November 26, 2026

The public step L-meta-1988 asks for a lower bound of 63 gates in a monotone binary AND/OR circuit. The designated output is the conjunction of up to two wires, supplied for free. The target returns true exactly when the active vertices include an incident point and line of the order-three projective plane. There are 26 input vertices and 52 incidence edges. [Posted statement](statement.json) · [Pinned upstream sources](sources.json)

| Result for the circuit before the free AND | Evidence |
|---|---|
| Every circuit needs at least **30 gates**. | Lean proves the literal posted implication with 30 as its conclusion. It also proves degree restrictions on any candidate of size at most 62. [Lean and derivation](lower/README.md) |
| Every circuit needs at least **31 gates**. | An independently reviewed decomposition forces seven wires to supply multiple gate inputs. An exhaustive enumeration bounds the weight rejected by each read-once factor. Lean verifies the split induction and counting inequalities. The passage from a circuit to the split certificate has a written proof. [DAG proof](read-once/DAG.md) · [Finite certificate](read-once/README.md) · [Formal components](support/README.md) |
| **64 gates suffice.** | Both designated wires are necessary in the displayed construction. Lean proves correctness on every input. A separate Python evaluator checks all 67,108,864 assignments. [Construction and replay](upper/README.md) |
| **64 is optimal** with OR preprocessing, individually sound AND products, and OR postprocessing. | The lower bound allows arbitrary sharing, two output wires, and direct OR paths to either output. A counting argument uses the incidence graph’s four-cycle exclusion and perfect matching. [Restricted lower bound](upper/README.md#lower-bound) |

The unrestricted minimum lies between 31 and 64. The posted threshold of 63 remains open. A smaller construction must exploit products depending on earlier products, or intermediate products that accept some edge-free input. Both designated wires can overaccept in valid constructions.

## What to try next

For a candidate below 63 gates, track how intermediate products reuse each other's outputs and which false inputs the other terminal excludes. In any two-factor representation, one operand must depend on all 26 inputs. Four such factors still cannot all omit an input, while five can. The certificates count the costs of omissions and the false-positive pairs compatible with an opposing factor. [Factor dependencies](transversals/README.md) · [False-pair compatibility](false-pairs/README.md) · [Strict supergraph examples](supergraphs/README.md)

Two limits narrow further searches. The exact fractional read-once covering optimum is 343/5. An explicit integral cover of size 96 prevents the logarithmic sharing argument alone from forcing an eighth shared wire. A separate enumeration caps the fixed uniform-witness elimination schedule at six flexible pins. [Fractional certificate](fractional/README.md) · [Integral cover](read-once/DAG.md#limit-of-the-factor-count) · [Elimination schedules](elimination-limit/README.md)

## Replay

Use the repository revision in `sources.json`, its pinned Lean 4.36.0 and Mathlib, Python 3.10 or newer, and a C++20 compiler. With the project dependencies available, run the following from this directory. The script verifies the upstream dependency digests, rebuilds the imported Lean modules, checks the local proofs, and repeats the finite enumerations.

```sh
bash replay.sh /path/to/pequalnp-proofs/lean
```
