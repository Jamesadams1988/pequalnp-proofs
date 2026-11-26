# The exact circuit size for L-meta-11030 and L-meta-11031

James Adams (Jamesadams1988), November 26, 2026.

The edge function on the nine vertices in L-meta-11030 has **minimum size 16** over unrestricted circuits of fan-in at most two with AND, OR and NOT gates. This refutes the counterexample requested by L-meta-11031. The lower bound follows by applying eleven already checked upstream theorems. A five-star decomposition gives a 16-gate circuit. [Exact statements and construction](Upper.lean) · [Composition](Exact.lean) · [Posted assignment](sources/assignment.json)

## Why fifteen gates cannot suffice

Budleigh’s L-meta-534 supplies a normal form for minimal nonconstant circuits. Danoszz’s L-meta-17110 reduces the target lower bound to nine cases indexed by the first gate. The checked cases, in index order 0 through 8, are L-meta-17303, 17305, 17307, 17313, 17315, 17317, 17319, 17321 and 17323. Each case concerns the exact twelve-edge graph in this assignment. Their proofs belong to MedicV2, grigorescu, skysmith, zakpgrove, puplux, Nabeel-javed and tmuniz1901-code. The public desk lists all eleven source digests as checked. The corresponding merged commits contain those exact files. [Proof hashes, authors and merged PRs](sources/dependencies.json) · [Normalization](https://github.com/open-goat/pequalnp-proofs/pull/630) · [Combining theorem](https://github.com/open-goat/pequalnp-proofs/pull/21993)

James matched the cases to the combining theorem, wrote the short composition and checked the matching upper bound. Lean 4.36.0 rebuilt the full normalization and combining proofs and verified the composition with the nine literal case types as parameters. Reversing the first two cases produced a type error. The component proof bodies have upstream checks. A fresh local build of case L-meta-17305 reached its 5,600 MB memory cap. The bounded replay therefore used the recorded upstream checks for the nine case proof bodies. The combined target has no new upstream verdict in this study. Adammcarter’s separate positive PR was open at the recorded head. [Lean assembly audit](CaseAudit.lean) · [Upstream PR](https://github.com/open-goat/pequalnp-proofs/pull/18201)

## How sixteen gates suffice

Center five stars on vertices 4, 5, 6, 7 and 8. Assign each of the twelve edges to one incident center. Form the OR of a star’s leaves and AND it with its center. All five stars together cost twelve gates, and four OR gates combine them. Lean verified the resulting circuit against the literal function for every input. An independent enumeration found all 47 nonempty bicliques are stars, the smallest vertex cover has five vertices, and a 16-gate witness agrees on all 512 assignments. [Lean circuit](Upper.lean) · [Independent enumeration and circuit](stars/README.md)

The separate formula calculation classifies 81 choices for a reusable first gate followed by an AND/OR formula. Exactly 26 choices allow size 16, and 55 require size 17. The exceptional optimal first OR on vertices 7 and 8 has an explicit formula outside the five-star partition constructions. [First-gate classification and replay](formula/README.md)

## Replay

Use Lean 4.36.0 and the pinned Mathlib packages in an upstream checkout at commit `94c10ce1d16334fe655533e3a493307d30459d91`. From this research directory, use the following command.

    bash replay.sh /path/to/upstream/lean

This checks the eleven source digests, the literal case signatures, the graph, the 16-gate witness and the assembly with the nine cases as parameters. With time and memory for the nine large upstream proofs, append `--full` to build each case in turn and check the closed theorem in Exact.lean. The assigned row permits the project import `PEqualNP.Defs`; this research composition imports checked outside modules. [Source audit](check-sources.py) · [Public checked-file export](https://data.pequalnp.com/data/desk/gaps.json)
