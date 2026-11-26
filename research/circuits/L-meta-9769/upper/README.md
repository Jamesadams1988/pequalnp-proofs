# A 124-gate circuit for the 104-edge literal DNF

The 42 inputs are the 21 points and 21 lines in the order used by L-meta-9769. Each point computes the OR of all of its incident line inputs and then ANDs that result with its point input. OR the 21 point outputs. The first point has degree four and each other point has degree five. The line ORs require 104−21 = 83 gates. Adding the 21 AND gates and 20 output ORs gives **124 gates**.

The Lean theorem `Row9769.PointStars.literalUpper124` uses the exact 104-term Boolean DNF in its original order and the upstream `PEqualNP.MetaComplexity.HasCircuitSize` definition. The terminal budget in the positive statement L-meta-9768 changes from 123 to 124. L-meta-9769 is the negation of the positive statement at 123. The 124-gate witness is compatible with either verdict at 123.

The proof builds on upstream's symbolic cover-circuit constructor and James Adams's earlier specialization for a different 40-input graph. It supplies the actual 42-input graph, proves the gate basis and census, and shows symbolically that the constructor computes the full left-associated desk DNF on every input. The `census` theorem gives 21 AND and 103 OR gates. `literalUpper124` has only the standard kernel axioms `propext`, `Classical.choice` and `Quot.sound`. [Pinned upstream cover constructor](https://github.com/open-goat/pequalnp-proofs/blob/e6a99b96b6c8eea0ce4874719a57f7817595a4b2/lean/PEqualNP/MetaComplexity/Helpers/CoverCircuitList.lean) · [Earlier 40-input witness](https://github.com/Jamesadams1988/pequalnp-proofs/blob/968bf0e91a8f9954310cdd137853913dd76ab943/research/circuits/L-meta-9802/Upper114.lean)

## Replay

Use an upstream checkout at `e6a99b96b6c8eea0ce4874719a57f7817595a4b2`, Lean 4.36.0 and the checkout's pinned Lake dependencies. Run the command below from this directory. It builds the cover helper and then checks the proof.

```sh
bash replay.sh /path/to/pequalnp-proofs/lean
```
