# Can the 114-gate circuit lose one gate?

Research by **James Adams** on L-meta-9802. The 40 input bits select vertices of a bipartite graph with 95 edges. The output must be true exactly when both endpoints of some edge are selected. The project asks for a monotone fan-in-two circuit with at most **113 total gates**. This package verifies a **114-gate** construction and gives lower bounds and reproducible searches for the same graph. The 113-gate question remains open. [Assigned statement](https://data.pequalnp.com/data/lemma/L-meta-9802.24b1f32b96d3.json) · [Opposite statement](https://data.pequalnp.com/data/lemma/L-meta-9804.220021d42b65.json)

## Unrestricted circuits

| Result | Evidence |
|---|---|
| At most 114 gates | The point-star construction has exactly 94 ORs and 20 ANDs. Lean checks it on all inputs, using the project's cover-circuit constructor. The literal theorem changes only the requested budget from 113 to 114. [Witness](Upper114.lean) · [Literal theorem](Literal114.lean) |
| At least 15 binary ANDs | For any monotone DAG, the binary AND gates give a bit string that separates false inputs whose pairwise unions are true. On this graph, 16,870 distinct neighborhood unions give such inputs, exceeding the 16,384 possible 14-bit strings. The entire witness family passed Lean's kernel. [Counting argument](Signature.lean) · [15-AND theorem](unions/FifteenAnd.lean) |
| At least 38 ORs, or 39 using a finite certificate | A connected ordering forces 38 distinct ORs. Starting with an induced six-cycle instead forces five ORs on its six vertices and another 34 on the remaining vertices. The second result uses Lean's native finite exclusion of four ORs on the six-cycle. An independent LRAT checker verifies that exclusion. [38-OR proof](Lower38.lean) · [39-OR proof](Lower39.lean) · [Finite certificate](../L-meta-4201/certificate/README.md) |
| At least 53 or 54 total gates | Adding the disjoint gate counts gives 53 with standard Lean axioms and 54 with the additional native-evaluation axiom for the six-cycle. [Combined bounds](Total54.lean) |

## Where a saving could occur

For circuits built from unions of inputs, followed by rectangles containing only genuine edges, at least 94 ORs and 20 products are necessary. The OR accounting permits unrestricted sharing of unions. Each product covers at most one edge of a 20-edge matching, even if later gates can delete edges for free. This makes the 114-gate star construction optimal in this class. A further obstruction applies to mixed star covers: omitting at least one vertex from each side requires 23 centers. [Rectangle lower bound](Rectangle114.lean) · [Mixed covers](CoverStability.lean)

We also tested two ways to introduce false positives and filter them out. Across all 16,895 ways to use one filtered two-sided rectangle alongside direct stars, the least cost is 114 even if the marking disjunction and filter AND are free. A different architecture intersects factors that each accept a union of two bipartite rectangles. It needs at least 255 factors to distinguish the cuts of an induced matching on nine edges. Each result has its own assumptions about which intermediate signals can be reused. [One-filter proof and enumeration](filters/README.md) · [Two-rectangle factors](TwoRectangles.lean)

A local search tried 35,744 connected windows across 64 star-circuit layouts. It looked for replacements using at least one fewer gate, allowed replacement gates to borrow unaffected wires, and compared outputs on all 95 minimal true and 16,870 maximal false inputs. No window yielded a smaller circuit. A more extensive search could replace several regions at once and reuse a newly built intermediate gate between them. [Search space, controls and full replay](rewrites/README.md)

## Relationship to PG(2,4)

Delete point 0 and line wire 22 from the 42-input plane and renumber the remaining vertices in order. This yields exactly the assigned graph. Restricting any full-plane circuit preserves its gate budget. In the other direction, the ten deleted edges can be restored using 12 gates. Any repair with access to all 42 raw inputs and only the punctured circuit's output needs at least 12 gates, even when it may use NOT. Thus a hypothetical 113-gate solution restores a 125-gate full-plane circuit. A cheaper restoration would have to reuse an internal signal or redesign the circuit. [Graph identification](IncidenceTransfer.lean) · [Circuit transfers](CircuitTransfer.lean) · [12-gate repair lower bound](PatchAllInputs.lean)

## Replay

Use a checkout of the upstream commit below with its pinned Lean 4.36.0 and Mathlib environment. Keep this directory beside the earlier L-meta-4201 directory on this fork. The Lean replay builds the upstream dependencies and compiles the local proofs in a fresh temporary directory. The census and filter replays use only Python’s standard library. The rewrite search also uses a C++20 compiler. [Pinned upstream checkout](https://github.com/open-goat/pequalnp-proofs/tree/0db966b0f50c36b7a95a561a869db13c8120ca5c) · [Project cover-circuit constructor](https://github.com/open-goat/pequalnp-proofs/blob/0db966b0f50c36b7a95a561a869db13c8120ca5c/lean/PEqualNP/MetaComplexity/Helpers/CoverCircuitList.lean) · [Upstream wire relabeling](https://github.com/open-goat/pequalnp-proofs/blob/0db966b0f50c36b7a95a561a869db13c8120ca5c/lean/PEqualNP/Outside/L_meta_4795.lean)

```sh
./replay.sh /path/to/pequalnp-proofs/lean
python3 unions/replay_census.py
python3 filters/check_filters.py
python3 rewrites/replay.py --full
```
