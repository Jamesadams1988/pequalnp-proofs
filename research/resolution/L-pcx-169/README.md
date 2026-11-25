# Ordinary resolution for five pigeons and four holes

James Adams · November 25, 2026

The smallest ordinary resolution **tree** for this formula has exactly **189 axiom leaves and 188 resolution steps**. Two independent computations give the lower bound. A Lean-checked tree attains it. The public assignment asks whether a proof with shared intermediate lines can fit in **149 total lines**. The shortest verified unrestricted construction in this package uses **157**, matching willakone’s merged upstream witness. [Tree proof and computations](tree/README.md) · [157-line construction and replay](witness/README.md) · [Upstream witness](https://github.com/open-goat/pequalnp-proofs/pull/13435)

Each of the five pigeons has four independent Boolean indicators, one for each hole. Five clauses say that each pigeon occupies at least one hole. Forty clauses forbid a pair of pigeons from occupying the same hole. Ordinary resolution combines two earlier clauses with opposite signs on the same variable. The project counts every original clause used and every resolution as one line. [Pinned formula and rules](https://github.com/open-goat/pequalnp-proofs/blob/e4bb613e0d57717d4eeec4ac147030c55b6e7f3a/lean/PEqualNP/Defs/ProofComplexity.lean) · [Assigned statement](https://data.pequalnp.com/data/lemma/L-pcx-169.4de6d1e40764.json)

| Which earlier lines can be reused? | Result for five pigeons and four holes |
| --- | --- |
| No reuse, count each occurrence | The minimum is 377 occurrences. Lean checks the correspondence between query trees and pure ordinary resolution in both directions. [Formal proof](tree/formal/README.md) |
| Reuse just the original axioms | The minimum is 233 lines. All 45 are necessary, and the 188 resolutions in a minimum tree suffice. [Computation and construction](tree/README.md) |
| Also reuse one specified positive Hall clause | The minimum is 223, 223 or 233, depending on whether the chosen subset contains one, two or three holes. Each number has a matching resolution certificate. [Exact bounds and witnesses](tree/one-hall/README.md) |
| Build a proof from the two canonical Hall expansions | The minimum is 157, even allowing independent choices of pivot pigeon or hole at every stage and global reuse of identical intermediate clauses. The counting argument extends to n+1 pigeons and n holes. [Proof and finite replay](mixed-hall/README.md) · [Independent exhaustive check](hall/README.md) |
| Use arbitrary shared ordinary resolution | A merged lower bound proves at least 101. A public construction uses 157. The desk's 149-line question remains open in this work. [Prior proofs and attribution](prior/README.md) |

An improved derivation for a single hole expansion takes 2, 5, 9 or 14 resolutions at levels 1 through 4. In the standard construction those costs are 2, 6, 12 and 20. Each improved block has an explicit proof and a matching lower bound from its indispensable premises. The finite replay checks every choice of pigeon set, hole set and chosen hole. A second exhaustive calculation allows the cheaper expansions at every stage. Even then the minimum stays at 157 when the final expansion pivots on a pigeon, or 174 when it pivots on a hole. [Local improvements and replay](elimination/README.md)

The pinned Lean source, independent counts and certificates make the results reproducible. The tests also distinguish ordinary unary resolution from the 149-line proof we published for a different pigeonhole encoding with two bits per pigeon. [Binary formula and witness](../L-pcx-133/README.md)
