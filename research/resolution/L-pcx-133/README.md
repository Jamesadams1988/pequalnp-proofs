# A 149-line refutation for five pigeons and four holes

James Adams · November 25, 2026

The binary pigeonhole formula says that five pigeons can occupy four holes without a collision. Here each pigeon has two bits naming its hole. A refutation derives a contradiction from the 40 clauses that forbid each possible collision. This certificate uses all 40 starting clauses and 109 ordinary resolutions, for **149 lines**. All 149 contribute to the empty clause. The same certificate is valid under the project's resolution-over-linear-equations rules. [Lean proof, trace, and replay](witness/README.md) · [Independent verifier](review/README.md)

The upstream proof by stasana666 contains 156 lines. Another upstream proof, by macayaven, excludes every refutation using 95 lines or fewer. The certificate here saves seven lines compared with that 156-line witness. The public desk asks for at most **127**. Its sketch mentions a computed witness one line above its threshold but supplies no trace to replay. We do not know the unrestricted minimum. [156-line construction](https://github.com/open-goat/pequalnp-proofs/pull/13350) · [96-line lower bound](https://github.com/open-goat/pequalnp-proofs/pull/20778) · [Assigned statement](https://data.pequalnp.com/data/lemma/L-pcx-133.3fcf1e6c1f83.json)

## Where sharing matters

| Construction | Checked result |
| --- | --- |
| Ordinary resolution with shared lines | The certificate uses 42 lines more than once. Unrolling it into a tree produces 140 axiom-leaf occurrences. [Trace analysis](search/bounded-search.md) |
| Query one pigeon's hole at a time and name a collision | Exactly 120 leaves are necessary and sufficient, even if a question can test any subset of holes. Disjoint product partitions labeled by a colliding pair require at least 100 boxes. [Methods and code](queries/README.md) |
| Derive each pair's inequality separately, then use a tree | A four-variable pair derivation takes exactly 11 lines. Ten such derivations plus a tree that can query arbitrary parities take at least 128 lines. [Derivation and lower-bound certificate](pair-route/README.md) |
| Derive three-pigeon Hall clauses without sharing intermediate lines, then use only those clauses | At least 20 Hall clauses and 159 total lines are necessary. There are three minimum families of 20. [Cover classification](hall/README.md) |

A next search can use a parity involving two pigeons and allow the resulting line to feed multiple later inferences. That permits sharing across pair derivations and in the final proof. The present trace gives a concrete baseline on which to measure any saving.

The witness imports only `PEqualNP.Defs` and was checked with Lean 4.36.0 at upstream revision `68d8de6866df4e70ba92793c839867835e87b145`. Its only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`. The independent verifier also tests the certificate on all 1,024 assignments. The restricted lower bounds have their own proof and replay instructions in the linked folders.
