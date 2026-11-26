# Nine first-gate cases for L-meta-11020

The eleven accepted declarations prove the 16-gate lower bound for the exact twelve-edge function in L-meta-11020. Consequently the assigned negative twin L-meta-11021 is false. The proof is the application of the first-gate case split L-meta-17107 to normalization L-meta-534 and nine lower bounds. L-meta-17103 supplies the zero-pivot case of this graph.

| Pivot | Accepted theorem | Pivot | Accepted theorem | Pivot | Accepted theorem |
| --- | --- | --- | --- | --- | --- |
| 0 | L-meta-17103 | 3 | L-meta-17273 | 6 | L-meta-17279 |
| 1 | L-meta-17269 | 4 | L-meta-17275 | 7 | L-meta-17281 |
| 2 | L-meta-17271 | 5 | L-meta-17277 | 8 | L-meta-17283 |

[CaseAudit.lean](CaseAudit.lean) states all nine hypotheses with the complete upstream types and applies the actual combiner. [ExactLower.lean](ExactLower.lean) supplies the accepted theorems to this application. [UpperJoin.lean](UpperJoin.lean) and [ExactMinimum.lean](ExactMinimum.lean) combine it with the explicit 16-gate upper witness. The resulting statement is `IsLeast {t : ℕ | HasCircuitSize 9 target t} 16`.

[The single-file refutation](src/PEqualNP/Outside/L_meta_11021.lean) gives the same lower-bound consequence directly from upstream modules, using the canonical theorem name and the literal negation of the desk statement. [The statement file](../sources/negative.txt) is the negative desk row itself, for local verifier mode `refute`. Its source pin is `6284ae5ebdec19cb4bce06d15e190de3560bc099`. All eleven proof-source SHA-256 digests match the desk's checked registry at this pin. [Source manifest](../sources/dependencies.json)

The zero-pivot case can also be built in 87 compilation units with its original proof bodies. Its output feeds the package’s `--prebuilt` replay. [Zero-pivot build instructions](split17103/README.md)
