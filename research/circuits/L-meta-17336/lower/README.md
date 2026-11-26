# A 15-gate unrestricted lower bound and necessary conditions for equality

The nine-input edge function in L-meta-17336 needs at least **15 fan-in-at-most-two AND/OR/NOT gates**, irrespective of its first wire. The desk's negative statement requires a circuit of size at most 15 with one of seven specified first-wire functions. Therefore a qualifying witness must use exactly 15 gates.

## Two checked eight-input restrictions

Setting input 2 to false gives the exact function of the checked theorem L-meta-8455 after relabeling. In order of the original input numbers 0 through 8, the new labels are **3, 1, 8, 5, 6, 0, 7, 4, 2**. Label 8 is the pinned input. L-meta-8455 proves that the residual requires at least 14 gates. Input 2 is essential, and the false cofactor is nonconstant, so pinning it saves at least one gate by the project's full-basis `gate_elim` theorem. The same argument applies to input 3 using L-meta-8459 with labels **3, 1, 7, 8, 5, 0, 6, 4, 2**. [L-meta-8455](https://github.com/open-goat/pequalnp-proofs/blob/c468e9f20b8fea4dc13ef9abde683cb439979a1c/lean/PEqualNP/Outside/L_meta_8455.lean) · [L-meta-8459](https://github.com/open-goat/pequalnp-proofs/blob/c468e9f20b8fea4dc13ef9abde683cb439979a1c/lean/PEqualNP/Outside/L_meta_8459.lean)

The Lean transfers check the equality of all 256 cofactor values, the dependence and nonconstancy hypotheses, and the lower-bound implication from the precise eight-input theorem interface. The one-line files From8455 and From8459 instantiate these interfaces. Both upstream source digests agreed byte for byte with commit `c468e9f20b8fea4dc13ef9abde683cb439979a1c`. The local rebuild of the 8455 donor was stopped by Lean's explicit `-M 3200` memory cap in its interpreter, before writing an object file. The local transfer checks use the donor statements as hypotheses. The public upstream proofs supply those hypotheses.

## What equality forces

Assume a qualifying circuit has 15 gates. Normalize NOT to its first operand as in the official evaluator, and count each gate once even if the same raw wire appears in two input positions. Every gate must be reachable backwards from the output along effective input positions. Otherwise removing an unused gate and renumbering the later wires produces a circuit with at most 14 gates. Both x₂ and x₃ matter, so each has at least one effective direct reader.

Fix either input xᵢ to false. Each distinct gate directly reading it can be removed during constant propagation: an AND gives false, a unary NOT gives true, and an OR is an alias of the other operand or a constant. The contracted circuit computes the eight-variable residual. Since it needs 14 gates, exactly one original gate can directly read xᵢ. That gate cannot become a constant. If it were the output, the residual would be constant. Otherwise at least one later effective consumer also simplifies, saving two gates. Thus the sole reader must be a binary OR of xᵢ and a distinct wire U. U is independent of xᵢ, because it precedes the unique effective reader.

Whenever U is true, flipping xᵢ cannot affect that OR or any other part of the circuit. This rules out every other raw input xⱼ for U. Inputs 2 and 3 each have two neighbors, and any distinct vertices have at most one common neighbor. For j adjacent to i, start with just j selected. For nonadjacent j choose a neighbor of i that is not adjacent to j and start with j and that neighbor selected. Either assignment has U true and no induced edge, and turning on i creates an edge. Repeating xᵢ itself as both OR operands would give a constant under the false pin and is already excluded.

The same test rules out the designated first wire as U in six cases. Entries list the selected inputs before xᵢ is turned on.

| First wire | Test for x₂ | Test for x₃ |
|---|---|---|
| NOT x₅ | {6} | {6} |
| x₅ AND x₆ | {5,6} | {5,6} |
| x₅ AND x₇ | {5,7} | {5,6,7} |
| x₅ OR x₆ | {6} | {6} |
| x₅ OR x₇ | {7} | {5,6} |
| x₅ OR x₈ | {5,6} | {8} |

The remaining wire x₅ AND x₈ already implies the edge function, so the masking test supplies no exclusion for it. The reader-count conclusions use the constant-propagation argument above. Masks.lean checks the finite exposing assignments independently.

## Replay

In the upstream Lean project, build `PEqualNP.MetaComplexity.Helpers.PermInputs`. Compile `Transfer.lean` to `Transfer.olean` and put its directory on `LEAN_PATH` to check `Masks.lean` and `Transfer3.lean`. To check the unconditional instantiations, build the corresponding upstream donor module, compile `Transfer3.lean` to `Transfer3.olean`, and run Lean on `From8455.lean` and `From8459.lean`.
