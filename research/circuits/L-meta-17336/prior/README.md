# Numerical replay of grigorescu's L-meta-17335 candidate

The 135 explicit finite assertions in grigorescu's PR #22380 all evaluated to true in a compiled numerical replay. This checks the data and search computations of that prior candidate. The universal soundness argument connecting those computations to every fan-in-two circuit is separate. Upstream ran the Lean kernel check twice, each time reaching its 20-minute limit, and closed the PR unmerged with no verdict on the theorem. The author reported a successful local check. [Candidate and author](https://github.com/open-goat/pequalnp-proofs/pull/22380) · [Pinned source](https://github.com/open-goat/pequalnp-proofs/blob/d8cf13b117c0488da25b467d9bebe19b896323b5/lean/PEqualNP/Outside/L_meta_17335.lean) · [Intake disposition](https://github.com/open-goat/pequalnp-proofs/pull/22380#issuecomment-7179084232)

## What was checked

The candidate represents restrictions of wires and the target by integer bit masks. Its shared table has four layers of previously certified restriction bounds, with 4, 20, 27 and 9 entries. The common root excludes a circuit of fewer than 15 gates before any first-gate bonus. Allowing one specified first-gate function as an extra available wire leads to seven separate searches. Each search aims to exclude fewer than 15 **additional** gates. The option named `six` in the source contains seven entries. Each branch consumes the shared results and its own tables. The branches can be evaluated separately after the common tables.

| First gate | Additional restriction checks | Root batches | Measured numerical time |
|---|---:|---:|---:|
| NOT 5 | 7 | 1 | 8.1 s |
| AND 5,6 | 1 | 1 | 1.3 s |
| OR 5,6 | 4 | 5 | 11.4 s |
| AND 5,7 | 2 | 1 | 1.0 s |
| OR 5,7 | 4 | 5 | 13.4 s |
| AND 5,8 | 4 | 2 | 7.7 s |
| OR 5,8 | 3 | 6 | 14.5 s |

On the recorded run all 135 assertions took 60.37 seconds of elapsed time, with 59.96 seconds of user CPU time. This excludes compilation. The shared tests took about 2.9 seconds. The runtime depends on the machine; the checker returns failure immediately on any false assertion. The finite checks cover mask consistency, chart membership, closure of the projected search, adequacy of the root partitions, the branch-specific tables, and agreement of the packed target with the literal edge function.

A separate Python decoder evaluated the literal 12-edge predicate on each of the candidate's 1,756 active bit positions. These positions contain 267 distinct assignments, of which 210 are true and 57 false. The decoder checks that each packed target bit agrees with the graph on the corresponding nine-bit assignment. This table agreement alone does not establish any numerical lower bound for circuits.

## Replay

The scripts use Python 3.9 or later and the Lean 4.36.0 binary distribution, including `leanc`. Pass the path to an already reviewed copy of the pinned Lean file for an offline replay. With no argument the script first uses `Prior17335.lean` beside it if present, otherwise it fetches the immutable public source URL printed above.

```sh
LEAN_BIN_DIR=/path/to/lean-4.36.0/bin bash replay.sh /path/to/L_meta_17335.lean
```

The replay checks the source SHA-256, the declaration allowlist, each selected source item, and the complete generated-program SHA-256 before compiling. The allowlist contains the 208 numerical definitions and 135 concrete Boolean, natural equality or natural inequality assertions. The imported module in the generated numerical program is the Lean standard library. No theorem or proof script from the upstream file is executed. The translation replaces nondependent primitive recursors by their pattern-matching equations; it simplifies `st n f` to `f n`, `pos t` to the positive-number test, and `prd t h` to false at zero and `h (t−1)` otherwise. Native compilation evaluates the resulting predicates as ordinary programs. This uses the native compiler as part of the numerical computation.

Source SHA-256: `4defc64e8c1808d31eb16e4d092560256cadea0b1f32be2d604d9413002b10a2`. Git blob: `54c223702dd6958e34e50fca0027171a0fc71715`. Lean compiler version and source pin belong with any reproduced results. The underlying certificate, search and mathematical argument are due to grigorescu's prior submission.
