# Exact gate count for the L-meta-14503 graph

James Adams (Jamesadams1988) gives a restriction proof that this eight-vertex edge function needs exactly **12 fan-in-two gates**, even with unrestricted NOT. A 12-gate AND/OR circuit attains that bound. The desk statement asks whether allowing one NOT beats every AND/OR circuit. The theorem `assignedStatementFalse` proves its negation from the exact minimum. [Proof](ExactMinimum.lean) · [Literal desk statement](statement.txt)

## Lower bound

Fix vertex 2 to false. It is essential, and the remaining graph still contains an edge, so this restriction saves at least one gate. Vertex 5 is now a leaf at 1. Some choice at 5 saves two gates. In either branch vertex 1 is essential, and fixing it to false saves another gate. Both choices at 5 then give the same graph. Fixing vertex 3 to false saves a fifth gate and leaves the four-clique on vertices 0, 4, 6 and 7. The four-clique requires seven gates. Every unrestricted circuit for the original graph therefore has at least 1 + 2 + 1 + 1 + 7 = 12 gates. [Gate elimination by nicohabets, crediting sanchan](https://github.com/open-goat/pequalnp-proofs/pull/9322) · [Four-clique lower bound by hilelyos](https://github.com/open-goat/pequalnp-proofs/pull/13494)

The matching circuit takes the OR of four terms, `(x0 OR x4) AND (x6 OR x7)`, `x0 AND x4`, `x6 AND (x3 OR x7)`, and `(x1 OR x2) AND (x5 OR x7)`. These same four terms already appear in TSGut’s and Leg0shii’s public proposals for the opposite desk statement, L-meta-14502. TSGut’s proposal also establishes the exact unrestricted minimum of 12 using a search certificate. The proof here derives the lower bound by removing vertices down to a four-clique. [TSGut’s positive-twin proof](https://github.com/open-goat/pequalnp-proofs/pull/19176) · [Leg0shii’s positive-twin proof](https://github.com/open-goat/pequalnp-proofs/pull/19246)

## Replay

From this directory run `python3 verify.py` to check the actual Lean circuit on all 256 inputs, the restriction hypotheses, and both final clique tables. To replay the independent search through all four-input circuits of up to six gates, compile `check_clique.cpp` with a C++20 compiler and assertions enabled. [Truth-table replay](verify.py) · [Four-clique search](check_clique.cpp)

With the pinned Lean 4.36.0, Mathlib and `PEqualNP.Defs` built, run `bash check_exact.sh ../../../lean`. This checks the hashes of the two upstream helper modules, rebuilds them and prints the axiom dependencies of the exact minimum and the refutation. [Lean replay](check_exact.sh)

For the official local checker, use a prepared checkout of upstream commit `deb981891b48588ae04b07eb279c43a1ddf77b58`. The generator creates a diagnostic with only `PEqualNP.Defs` imported, embedding the cited helper sections. Its output path must be new. [Diagnostic generator](pack_refutation.py)

```sh
research_dir=$PWD
upstream=/path/to/pequalnp-proofs
proof=lean/PEqualNP/Outside/L_meta_14503.lean
python3 pack_refutation.py "$upstream" "$upstream/$proof" &&
  (cd "$upstream" && node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute)
```

The official local checker returned `ACCEPTED (refute)` for source SHA-256 `65d0576607e213d81fa4ec979f06f027faeff1f7a1ae2de144cca0426d2da4d7`. It kernel-checked 2,344 constants and reported only `propext`, `Quot.sound` and `Classical.choice`.
