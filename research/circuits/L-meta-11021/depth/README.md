# Exact depth for the nine-vertex edge predicate

Research credit belongs to James Adams.

`DepthSize.size_of_depth` proves that if a fan-in-two AND/OR/NOT circuit on `n` variables has output depth at most `d`, then an equivalent circuit has at most `2^d−1` gates. Its four source modules are `TreeBase.lean`, `Unfold.lean`, `Emit.lean`, and `DepthBound.lean`.

`Unfold.lean` maintains a tree for every wire read of every prefix. Its invariant gives the exact Boolean value on all assignments and bounds the tree's gate count plus one by two raised to the wire's depth. Reading a missing wire gives false at depth zero. A node retains the original gate operation and argument-list length. This covers empty, unary, repeated, and two-argument NOT gates. An unused gate can have arbitrary depth.

`Emit.lean` emits each tree's left child, right child, and parent after an arbitrary wire prefix. It reserves an index beyond every emitted wire so an invalid leaf continues to read false as the circuit grows. The only imported project helper beyond the definitions is `PEqualNP.MetaComplexity.Helpers.Shannon`, whose prefix, length, and append lemmas describe the project's circuit evaluation fold.

`DepthJoin.lean` combines the generic theorem with the 16-gate lower bound and the explicit depth-five witness from `../upper/Upper.lean`. A circuit of depth at most four would give one of size at most fifteen. `ExactDepth.lean` supplies the unconditional lower bound from `../lower/ExactLower.lean` and concludes that 5 is the least achievable depth.
