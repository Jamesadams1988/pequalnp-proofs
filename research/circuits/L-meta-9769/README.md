# Circuit bounds for the punctured plane of order four

James Adams (Jamesadams1988) · L-meta-9769

**The exact minimum is between 51 and 124 gates, inclusive.** Lean checked both endpoints for the 104-term Boolean function on 42 inputs, allowing binary AND/OR and unary NOT. The desk asks whether every such circuit needs at least 124 gates. The remaining question is whether any circuit of size 51 through 123 computes this same function. [Exact desk statement](statement.json) · [Public desk](https://pequalnp.com/desk/step?gap=L-meta-9769)

**Unrestricted lower bound.** The 51-gate proof combines ten restrictions that each save two gates with 27 restrictions that each save one. Five essential inputs survive, requiring at least four further gates. The proof uses the project’s gate-elimination theorems, which apply even when internal gates compute nonmonotone functions. [Lean lower bound](lower/Terminal51.lean) · [Restriction sequence and witnesses](lower/Terminal51.md) · [Upstream elimination theorem](https://github.com/open-goat/pequalnp-proofs/blob/e6a99b96b6c8eea0ce4874719a57f7817595a4b2/lean/PEqualNP/MetaComplexity/Helpers/PermInputs.lean)

**Unrestricted upper bound.** A point-centered star construction uses 21 AND gates and 103 OR gates. The Lean theorem compares the circuit with the literal desk expression for every Boolean assignment. The desk already reported a construction of this size. [Lean witness](upper/Literal124.lean)

**Reusable lower-bound certificate.** A second derivation branches on an input and simplifies each resulting Boolean function to individual input terms and remaining edges. The published verifier checks all 1,024 leaves against the literal statement. The generic branching rule and its 46-gate control have Lean proofs. [Method and replay](adaptive/README.md)

## Sharp bounds for restricted computations

| Model | Result |
|---|---|
| Individually safe AND products of shared ORs of signed input literals, followed by AND/OR/NOT gates that see only those products | Exactly 124 gates. Using centers on both sides costs at least 125. If each side also omits a center, the minimum rises to 127. Both mixed bounds are attained. [Proof, hypotheses and census](search/README.md) |
| AND/OR/NOT formula trees | At least 17 distinct input variables must occur twice or more, giving at least 59 input occurrences. The largest induced star forest has exactly 25 vertices. The incidence proof also applies to a single deleted incidence in any plane of order four. [Proof and independent finite check](formula/README.md) |

## Replay

Use Python 3.10 or later, a C++20 compiler, and a Lean checkout of upstream commit `e6a99b96b6c8eea0ce4874719a57f7817595a4b2` with the pinned Mathlib package cache. The project uses Lean 4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The replay verifies the imported project source files, checks the Lean proofs, regenerates the adaptive certificate, and reruns both star-forest enumerations plus the signed-product controls.

```sh
bash replay.sh /path/to/pequalnp-proofs/lean
```
