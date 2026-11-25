# Independent review of the BPHP(5,2) certificate

From this directory, replay the certificate with Python 3.10 or later. To check a separate certificate, pass its path as a positional argument.

```sh
python3 verify.py --expect-lines 149
```

The 149-line witness uses all 40 collision axioms and 109 resolutions. Every line contributes to the final empty clause. The verifier reconstructs each result from its two earlier parents, checks the pivot signs, and tests the implication on all 1,024 assignments to the ten input bits. It also supports semantic weakening by testing the implication from its single parent. These counts give an upper bound of 149. The assigned threshold is 127. [Official row](https://data.pequalnp.com/data/lemma/L-pcx-133.3fcf1e6c1f83.json)

`QueryTree.lean` proves a separate theorem for ordinary tree-like resolution. Starting at the empty clause, `fromRefutation` follows the parent whose pivot literal is false. It produces a tree of fresh bit queries with at most the proof tree's number of axiom-leaf occurrences. Semantic weakening between ordinary clauses adds no query. At each terminal leaf, `collision` proves that the partial assignment fixes two distinct pigeons to one complete hole. Unrolling a shared proof can copy a line many times. This leaf count therefore gives a lower bound for the tree model only. Pivots in the theorem are individual variables. [Formal reduction](QueryTree.lean)

After building the repository's pinned Lean project, run from its `lean/` directory:

```sh
review_dir=../research/resolution/L-pcx-133/review
lake env lean --root="$review_dir" "$review_dir/QueryTree.lean"
```

Both printed theorems use `propext`, `Classical.choice`, and `Quot.sound`.
