# Exact circuit size for each OR on wire 9

For the twelve-edge Boolean function in [the witness module](../upper/Witnesses.lean), a fan-in-two circuit whose wire 9 computes `x 5 || x j` on every input has minimum size 16 for each of `j = 6, 7, 8`. The minimum ranges over all circuits satisfying those conditions, including circuits using NOT and sharing gate outputs. The upper witnesses use AND and OR. The wire constraint is semantic. The minimum over the union of all seven allowed first-wire choices is also 16, since the lower bound covers the union and any one of the three OR witnesses attains it.

[ExactOrFirst.lean](ExactOrFirst.lean) defines the feasible sizes as a set of natural numbers and proves that 16 is its least member. Its parameter is the literal proposition of the upstream lower bound. The proof supplies the three witness theorems from the existing upper module and applies the OR branch of the lower bound to an arbitrary feasible circuit.

[From17335.lean](From17335.lean) closes the result with `PEqualNP.Outside.L_meta_17335`, proved by tmuniz1901-code in [upstream PR 22678](https://github.com/open-goat/pequalnp-proofs/pull/22678). The [merged proof source](https://github.com/open-goat/pequalnp-proofs/blob/589779f8cf91f38596cfb4785099c50376e665fe/lean/PEqualNP/Outside/L_meta_17335.lean) has SHA-256 `7720c4b1bfed9ccab4ae664a157df82713f850bde5f8f79c5901a4d5d175099f`.

Run the following with the upstream Lean toolchain, from a copy of this directory next to the existing upper directory. The first command checks the conditional theorem and rebuilds the witnesses. The second checks the closed theorem against an upstream project with the accepted lemma already built.

```sh
./replay.sh /path/to/pequalnp-proofs/lean ../upper/Witnesses.lean
./replay.sh /path/to/pequalnp-proofs/lean ../upper/Witnesses.lean --closed
```

Upstream accepted head `59ec8ae2312b523afe98293452faaff3d8f96805` at 01:21:11 UTC on November 26, 2026. It merged at 01:24:28 UTC. The next public export recorded the proof and withdrew L-meta-17336. For wire 9 equal to NOT of input 5 or an AND with input 6, 7 or 8, these sources leave a one-gate interval from 16 through 17. The unrestricted parent graph still needs the first-gate case for pivot 0. [Checker verdict](https://github.com/open-goat/pequalnp-proofs/pull/22678#issuecomment-7179688428) · [Recorded sources](verdict.json) · [Remaining parent case](https://github.com/open-goat/pequalnp-proofs/pull/22490)

The conditional replay passed with Lean 4.36.0. A fresh local compilation of the merged lower-bound source reached the configured 9,000 MB Lean memory limit. The accepted upstream check supplies that proof in the result reported here.
