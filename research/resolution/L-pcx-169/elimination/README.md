# The local cost of adding one pigeon

James Adams. In the unary pigeonhole formula for five pigeons and four holes, a Hall clause says that some pigeon in a specified group occupies a hole outside a specified set. This package proves the minimum number of ordinary binary resolution steps for each block of the fixed pigeon-prefix construction. It also includes an independent ordered variable-elimination experiment.

## The exact local bound

Fix a nonempty set of *k* holes, and use the first *k* pigeons as the old pigeons. The target says that one of these pigeons or the new pigeon occupies a hole outside the set. The premises available to this local proof are:

- The new pigeon's ordinary four-hole row clause.
- For each of the *k* selected holes, a previously derived Hall clause. It says that an old pigeon occupies that particular hole or a hole outside the set.
- For each old pigeon and selected hole, the binary clause forbidding that old pigeon and the new one from occupying the hole together.

Every one of the **1 + k + k²** premises is necessary. To see this for the new row, leave the new pigeon absent and occupy the selected holes with old pigeons. For a missing predecessor at hole *h*, place only the new pigeon in *h* and occupy each other selected hole with old pigeons. For a missing collision between old pigeon *i* and the new pigeon in *h*, use the preceding assignment and also put *i* in *h*. All outside-hole variables are false. Each assignment falsifies the target while satisfying every other local premise.

In any binary proof DAG, working backwards from the target, replacing one pending line by both parents increases the number of distinct pending lines by at most one. Each critical assignment must reach its own premise, so at least **k + k²** binary resolutions are necessary. This permits arbitrary intermediate clauses and reuse within the block. The ordinary construction attains the bound. For each selected hole, resolve its predecessor with the *k* collision clauses to obtain a conditional that excludes the new pigeon from that hole unless some old pigeon is outside. Resolve the *k* conditionals with the new row.

| Selected holes | Blocks | Minimum resolutions per block |
| ---: | ---: | ---: |
| 1 | 4 | 2 |
| 2 | 6 | 6 |
| 3 | 4 | 12 |
| 4 | 1 | 20 |

The sum is 112 resolutions. Adding the 45 distinct original axioms gives 157 lines when each block uses its designated local premises and has its own intermediate lines. The question for an unrestricted ordinary resolution proof asks for at most 149 lines. It allows other premises and intermediate sharing across blocks. [Official resolution and PHP definitions](https://github.com/open-goat/pequalnp-proofs/blob/e4bb613e0d57717d4eeec4ac147030c55b6e7f3a/lean/PEqualNP/Defs/ProofComplexity.lean)

`Row169.HallLocal.joinsNeededOfModels` proves the general binary-DAG bound. `Row169.HallLocal.eachBlock` instantiates it using the official resolution rule and checks the critical assignments for all 15 nonempty hole sets. Its axioms are `propext`, `Classical.choice`, and `Quot.sound`. `Row169.HallLocal.totalJoins` checks the sum using `propext`.

## Shorter proofs for a hole expansion

A different local premise set supports a shorter construction. Choose a hole *h* in the selected hole set *T*, and write *S* for the *m = k + 1* active pigeons. For each pigeon *r*, take the Hall clause on the remaining pigeons and the holes *T* excluding *h*. This includes every positive literal in column *h* except the one for *r*, plus literals outside *T*. Also take every pairwise collision axiom within column *h*. The goal is the parent Hall clause for *S* and *T*.

Choose a last pigeon *r*. Starting from the predecessor that omits it, resolve on each earlier pigeon's column variable against its collision with *r*. The result contains the negative literal for *r*. Every other predecessor contains the positive literal for *r*. Apply the construction recursively to those other predecessors and to collisions among the earlier pigeons, carrying that positive literal to the result. Resolve the two branches on *r*. With one active pigeon the corresponding predecessor is already available. All outside-hole literals stay positive, so the same derivation on the full unary variables ends with exactly the parent Hall clause.

This proof uses all *m* predecessor clauses and all *m(m−1)/2* collisions exactly once. Its binary resolution count is their sum minus one. This is the minimum for arbitrary local DAG proofs from this stock. To witness the necessity of the predecessor omitting *r*, set just *r*'s variable in column *h* to true. To witness a missing pair collision, set just those two variables to true. Both assignments falsify the parent clause and exactly the named premise.

| Selected holes *k* | Resolutions in the standard hole expansion | Exact minimum with this local stock |
| ---: | ---: | ---: |
| 1 | 2 | 2 |
| 2 | 6 | 5 |
| 3 | 12 | 9 |
| 4 | 20 | 14 |

For the five-pigeon root in column zero, `Row169.ColumnRoot.attained` and `Row169.ColumnRoot.necessary` verify both directions of the exact 14-resolution bound in Lean. The stock contains five explicit predecessor clauses and ten collision clauses. Both theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

The script `hole_blocks.py` constructs the whole trace, checks the literal-set resolution rule, verifies that every line except the result has exactly one use, and tests the critical assignment for every source. It checks all 224 choices of *S*, *T* and *h* in the five-pigeon instance. To emit the 14-resolution example, run `python3 -B hole_blocks.py --root-trace root14.json`. Its five predecessor lines are inputs to the local block and must themselves be derived in a full refutation. The global cost depends on which predecessor clauses the overall construction needs.

## Ordered elimination

`eliminate.py` applies Davis–Putnam elimination. At each pivot it discards tautologies and clauses subsumed by a retained clause. It records actual binary resolutions and extracts just the ancestors of the final empty clause. A second implementation reconstructs that trace with sets of signed literals. In the two deterministic replay trials, pigeon-major order gives 248 lines and hole-major order gives 174. These are measured witness lengths.

Replay the Lean proofs and the two Python trials with the upstream Lean 4.36.0 project and its built dependencies:

```sh
./replay.sh /path/to/upstream/lean
```

The Python search uses only the standard library. To save the 174-line trace separately, run:

```sh
python3 -B eliminate.py --rounds 2 --seed 420 --output ordered.json
```
