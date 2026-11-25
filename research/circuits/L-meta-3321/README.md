# Clean AND gates in incidence circuits

Research by James Adams (Jamesadams1988).

L-meta-3321 asks whether every monotone circuit computing bipartite incidence on a graph without a four-cycle has an equally small or smaller circuit with clean AND gates. Here an input selects some points and lines. The target is true when it selects both endpoints of an edge. A clean AND that fires must either fire on one of the two one-sided projections or have an edge in the input. Every AND must also be off on every singleton. This folder proves the requested conclusion for all forests, for a further family with well-separated branch vertices, and for every four-cycle-free N-by-N incidence graph with N ≤ 3. The unrestricted problem remains open. [Desk statement](https://pequalnp.com/desk/step?gap=L-meta-3321) · [Literal small-case theorem](DeskControls.lean)

## Families with a size-preserving replacement

For a nonempty edge set and vertex cover T, group the edges into stars centered at vertices of T. Each star takes the AND of its center with the OR of its assigned neighbors. Whenever that AND fires, a specific edge is active. Combining the stars uses at most the number of edges plus the size of T minus one gates. The construction proves correctness, backward wire references, the size bound and the behavior of every AND. It extends the upstream star construction. [Clean construction](CleanCover.lean) · [Upstream construction](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/PEqualNP/MetaComplexity/Helpers/EdgeUpperMono.lean)

For a minimum cover, upstream lower bounds show that the construction fits in the original circuit budget in two cases. The first includes every forest, with isolated vertices and the empty graph allowed. The second requires every cycle to have length at least seven and every walk between distinct vertices of degree at least three to have length at least seven. The reduction isolates two remaining possibilities for a cyclic graph without a four-cycle. It either contains a six-cycle or, with every cycle longer than six, has two distinct branch vertices joined by a walk of length below seven. [Family proofs](ForestBridge.lean) · [Remaining cases](RemainingCases.lean) · [Six-cycle characterization](HexagonCases.lean) · [Upstream forest lower bound](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/PEqualNP/MetaComplexity/L104.lean) · [Upstream separated-vertices lower bound](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/PEqualNP/MetaComplexity/L204.lean)

On three vertices per side, Lean classifies every four-cycle-free relation as a forest or the complement of a permutation matrix. The latter is a six-cycle. We relabel the upstream lower bound and construct a clean eight-gate circuit attaining it. The proof for all side sizes up to three uses the ordinary kernel and includes the exact desk conclusion. The upstream six-cycle lower bound credits sanchan's earlier small-graph proof. [Six-cycle proof](SixCycle.lean) · [Classification](Three.lean) · [All side sizes through three](UpToThree.lean) · [Upstream lower bound](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/PEqualNP/Outside/L_meta_4795.lean)

## What a gate test can establish

For any monotone wire, checking its inclusion-minimal activating inputs is sufficient and necessary for cleanliness. Each such input must lie on one side or contain an edge. Minimality can be tested by deleting one selected vertex at a time. The wire monotonicity argument adapts the upstream wire evaluation proof. A separate pass decides the all-singletons condition. [Minterm theorem](Minterms.lean) · [Singleton test](OneHot.lean) · [Upstream wire proof](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/PEqualNP/MetaComplexity/Helpers/LowMergeWires.lean)

Checking only pairs can miss a dirty AND even when every gate affects the output. A ten-gate circuit computing the three-edge matching passes all singleton and mixed nonedge-pair tests. One AND nevertheless fires on a point and two nonincident lines and goes dark on both projections. A clean five-gate circuit computes the same function. The parametric construction gives an analogous obstruction at any chosen weight k ≥ 2. On the matching of size k, every AND passes the projection test on rejected inputs of weight below k, and one explicit rejected input of weight k fails it. These examples explain a limitation of testing an existing circuit. They leave open the existence of an equally small clean replacement. [Ten-gate circuit and five-gate control](PairTests.lean) · [Matching family](WideNet.lean) · [Proof for every gate](AllGates.lean)

A separate six-cycle example checks all 64 inputs and shows why a shared dirty AND cannot always be bypassed to either operand or erased at a single OR reader. A potential normalization proof must account for the effect on multiple readers at once. The formal comparison with L-meta-3451 also shows that the full cleanliness clauses imply that weaker singleton and nonedge-pair specification. [Shared-gate example](shared_or_example.py) · [Comparison](WeakerSibling.lean)

## Replay

Use Lean 4.36.0 and the Mathlib revision pinned by the upstream checkout at commit `0d13d43033f698f23269242b248d85754064a1e4`. With that checkout's Mathlib cache installed and its Lean toolchain on PATH, run the following from this folder. The Lean script builds three upstream dependencies, then checks the research modules into a temporary directory. The extra imports serve the family proofs on this research branch. The official desk permits only `PEqualNP.Defs` for a submission. [Upstream build configuration](https://github.com/open-goat/pequalnp-proofs/blob/0d13d43033f698f23269242b248d85754064a1e4/lean/lakefile.toml)

```sh
bash check_lean.sh /path/to/pequalnp-proofs/lean
python3 check_pair_tests.py
python3 shared_or_example.py
```

The finite experiment independently enumerates all labeled four-cycle-free relations through size three, checks each clean witness against all inputs and tests smaller circuit sizes with SAT. At size three it finds 334 labeled relations in 16 classes under row and column permutations and exchange of the two sides. The proof for all these relations above is independent of the SAT encoder. [Finite experiment and certificate replay](finite/)
