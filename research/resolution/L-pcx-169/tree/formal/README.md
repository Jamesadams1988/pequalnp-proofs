# Ordinary resolution trees and bit-query trees

For every CNF and every leaf budget, `sameLeafBudgets` proves that a pure ordinary resolution refutation tree exists within that budget exactly when a Boolean query tree can identify a falsified input axiom within it. The conversion back to resolution drops a branch when the pivot literal is absent from its derived clause. All remaining internal nodes use the project's ordinary syntactic resolution rule. `serialize` emits a project derivation with exactly `2L − 1` lines for a tree with `L` axiom-leaf occurrences. [Lean proofs](OrdinaryTree.lean)

`unaryTerminal` identifies the two kinds of terminal partial assignment in the unary PHP formula. Some row is entirely false, or two different pigeons are both true in the same column. It covers the full Boolean matrix, including assignments where a pigeon occupies more than one hole. The numeric optimum of 189 leaves comes from the separate finite dynamic program. The formal equivalence accounts for tree occurrences, and the official 149-line question permits shared derived lines. [Input definition](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/ProofComplexity.lean)

From the pinned upstream checkout's built `lean/` directory, run `sh /path/to/tree/formal/check.sh`. The script checks both sources and their printed axiom dependencies in a temporary build directory. `QueryTree.lean` is the shared dependency from the BPHP tree analysis. The printed theorems use `propext`, `Classical.choice`, and `Quot.sound`.

From this directory, run the independent certificate replay with Python 3:

```sh
python3 verify_tree.py --expect-377-tree ../tree377.json
```

The certificate has 65 pigeon-axiom leaves, 124 collision-axiom leaves, and 188 resolutions. Checks reconstruct each signed pivot and its exact resolvent, require the final empty clause, and verify that every previous line occurrence has exactly one use. Equal clauses can occur at multiple nodes. The 377 occurrences contain 197 distinct clauses.
