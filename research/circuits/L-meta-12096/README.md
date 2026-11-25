# A thirteen-gate witness and an exact finite computation for L-meta-12096

James Adams (Jamesadams1988) studied the six-input table `0xfe80fe00fe00e800`. The public conjecture asks whether every AND/OR/NOT circuit for this table has a monotone AND/OR circuit of at most the same size. Lean checks a 13-gate monotone witness on all 64 inputs. Exhaustive C++ search rules out every circuit of at most eleven binary gates, even when any wire or output may be complemented for free. A second finite search excludes twelve-gate monotone circuits. Together these results give an exact minimum of **13 gates** for both ordinary and monotone circuits. Lean verification of the full-table finite exclusions remains open. [Public statement and project sketch](https://data.pequalnp.com/data/lemma/L-meta-12096.c30be22116ce.json) · [Negative twin](https://data.pequalnp.com/data/lemma/L-meta-12097.46807904eac9.json)

## How the two results fit together

An ordinary circuit without NOT is already monotone. An ordinary circuit containing a NOT must use at least twelve binary AND/OR gates according to the finite search. With a physical NOT, its total size is therefore at least thirteen, so the 13-gate witness fits its budget. The replacement claim needs only the first exclusion. The second establishes the exact minimum. Lean checks the general implication and its specialization here. [Conditional proof](Replacement.lean) · [Search, pruning and normalization](signed-search.md)

Write the inputs as `a,b,c,d,e,f`. The output is true precisely when `2(a+b+c) + 5d + e + f ≥ 8`. The witness computes the three thresholds of `a,b,c` and the two thresholds of `e,f`, then combines these five signals with `d`. Five additional gates are sufficient and necessary when the combiner receives those six features. The lower bound for this architecture uses six pairs of legal inputs, each exhibiting the need for a different feature. [Construction and threshold identity](ThresholdCircuit.lean) · [Exact five-gate combiner](FeatureLower.lean)

Identifying one of `a,b,c` with either `e` or `f` recovers a previously proved nine-gate function. This gives a Lean-checked lower bound of nine gates for every full-table circuit. If its first gate combines the identified pair, that gate disappears and the lower bound rises to ten. This argument uses willakone’s five-input certificate and Nico Habets’s relabeling theorem. [Identification proof](Diagonal.lean) · [Five-input certificate](https://github.com/open-goat/pequalnp-proofs/pull/12916) · [Relabeling theorem](https://github.com/open-goat/pequalnp-proofs/pull/9322)

## All twelve restrictions

The sizes below agree for monotone circuits, ordinary AND/OR/NOT circuits, and circuits with free complementation. Lean checks the monotone witnesses on all 32 inputs of each restriction. An independent C++ replay excludes smaller binary circuits by retaining every still-needed signal and checking which assignments it distinguishes. [Lean witnesses](FaceWitnesses.lean) · [Finite lower bounds](face_lower.cpp)

| Input fixed | False | True |
|---|---:|---:|
| Each of a, b, c | 6 | 8 |
| d | 4 | 8 |
| Each of e, f | 8 | 7 |

## Reproduce the checks

Use a C++20 compiler with unsigned 128-bit integers and Python 3. The full-table search prints `fits=0` for the eleven-gate budget. The positive controls also confirm it recognizes a circuit that needs a complemented input.

```sh
g++ -std=c++20 -O3 face_lower.cpp -o face_lower && ./face_lower
g++ -std=c++20 -O3 signed.cpp -o signed && python3 replay_controls.py
./signed 11 0
./signed 12 1
```

The Lean files use upstream commit `ae067003624a27d3205bb5194ddb4bc50bde97c5`, Lean 4.36.0 and the Mathlib revision in the upstream manifest. Set `research_dir` to this directory's absolute path and run from the upstream checkout's `lean` directory.

```sh
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.Support PEqualNP.Outside.L_meta_4795 PEqualNP.Outside.L_meta_8646
replay_dir=$(mktemp -d)
lake env lean --root="$research_dir" -o "$replay_dir/ThresholdCircuit.olean" "$research_dir/ThresholdCircuit.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/Replacement.lean"' sh "$replay_dir" "$research_dir"
for module in FeatureLower Diagonal FaceWitnesses; do
  lake env lean "$research_dir/$module.lean" || exit 1
done
```

## Remaining Lean certificate

The Lean reduction below packs 128 positive/negative pairs into 256-bit words. The sample covers all 64 assignments. Lean verifies the six input words, coverage of every possible first gate and the implication from the resulting 60 branch obligations to monotone replacement. Each outstanding obligation excludes the target with ten binary gates left after that first move. Discharging these obligations is sufficient for the public positive conjecture. Certifying the separate twelve-gate monotone exclusion is only needed for the exact minimum. [Lean reduction and 60 branches](SignedFrontier.lean) · [Upstream signed-circuit checker used by the reduction](https://github.com/open-goat/pequalnp-proofs/blob/ae067003624a27d3205bb5194ddb4bc50bde97c5/lean/PEqualNP/Outside/L_meta_14930.lean)

The reduction imports the project's definitions. Replay it in the same upstream environment with `lake env lean "$research_dir/SignedFrontier.lean"`.

### Partial certificates for first-gate case 13

In this case the first gate is the OR of inputs 0 and 4, and both inputs are available for later use. Lean checks the circuit witness together with the exact posted conclusion under the remaining first-gate hypotheses. The combined development used only the allowed `PEqualNP.Defs` import when tested as one file. [Conditional theorem](FrontierGoal.lean)

A state is impossible if two original inputs have opposite required outputs but equal values on every available wire. Future gates must give both inputs the same result. Lean proves this for every remaining gate budget and proves that testing the condition leaves the search result unchanged. One actual descendant passes the original 128 pair tests yet cannot distinguish input rows 8 and 25. [General proof](Prune.lean) · [Packed row test](MaskPrune.lean) · [Search equivalence](PrunedSearch.lean) · [Checked example](Head13.lean)

Lean closes a subtree with eight gates remaining and several subtrees with seven gates remaining. The path indices below are zero-based positions among the admitted choices at each level.

| Path starting at first-gate case 13 | Evidence |
|---|---|
| 13 → 27 → 66 | Both transitions are admitted. Lean rules out the entire remaining eight-gate search. [Eight-gate certificate](Child27Case.lean) |
| 13 → 0 → 1 | Sixteen distinct children of this state are admitted and excluded with seven gates remaining. [Grouped exclusions](SmallGroup.lean) |
| 13 → 0 → 1 → 102 | All four transitions on the path to a terminal state were verified. The seven-gate parent is also excluded. [Kernel proof](Branch13.lean) |
| 13 → 0 → 12 → 55 | The exact generator gives 73 next choices. Lean verifies their six-gate exclusions in contiguous groups and then rejects the parent. [Generator and group proof](CompactLayer.lean) · [Uniform groups](UniformChunks.lean) · [Subtree certificate](UniformPilot.lean) |

Run `bash "$research_dir/replay_lean.sh"` from the pinned upstream `lean/` directory to compile these modules in dependency order. Input permutations of the first three variables and the last two variables preserve the target. Lean checks that these twelve permutations reduce the 60 first-gate cases to **18 representatives**. A proof of the ten-gate exclusion for each representative now suffices for the exact posted theorem. All eighteen representative cases remain open in Lean. [Symmetry proof](Symmetry.lean) · [Exact conditional statement](FrontierGoal.lean)
