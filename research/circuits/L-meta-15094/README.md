# Adding a fresh AND or OR input costs exactly one gate

Let a nonconstant Boolean function have minimum unrestricted fan-in-two circuit size *m*. Combining its output with a fresh input using AND or OR gives a function with minimum size **m + 1**. James Adams (Jamesadams1988) formalized both operations in Lean and used the result to classify extensions of a five-input function from the public proofs repository. [General theorem](FreshOutput.lean)

Appending one gate gives the upper bound. For the lower bound, fix the fresh input to true for AND or false for OR. This recovers the original nonconstant function. Since both output values occur, the fresh input is essential, so fixing it removes at least one gate. The formal statement covers every size budget. It also transfers a same-budget monotone replacement from the original function to the extension. The proof uses Nico Habets’s gate-elimination and relabeling lemmas, which credit sanchan. [Gate-elimination proof](https://github.com/open-goat/pequalnp-proofs/pull/9322) · [Earlier elimination work](https://github.com/open-goat/pequalnp-proofs/pull/1992)

Nonconstancy matters. Under the project’s circuit semantics, constant false has a zero-gate circuit. Its AND with a fresh input is still constant false and takes zero gates.

## The assigned table

The six-input table `0xa880888088800000` is the AND of input 0 and the five-input function `0xe8a8a800` on inputs 1 through 5 in order. Odinfree’s merged L-meta-8637 proof supplies the eight-gate unrestricted lower bound for that function. A nine-gate monotone formula attains the resulting bound for the full table. Stasana666 and Nico Habets both previously proved the nine-gate result for the exact positive statement, using this same restriction. [Five-input certificate](https://github.com/open-goat/pequalnp-proofs/pull/12773) · [Six-input replay](ExactMinimum.lean) · [PR #19866](https://github.com/open-goat/pequalnp-proofs/pull/19866) · [PR #20007](https://github.com/open-goat/pequalnp-proofs/pull/20007)

## Counting the extensions

Start with that five-input function or its De Morgan dual. Permute the original inputs freely. Each additional labelled input appears exactly once, at an outer AND or OR gate in any order. The Lean induction proves that a chain of *k* such gates adds exactly *k* to the unrestricted minimum. [Chain theorem](OuterChain.lean) A monotone circuit attains the same size throughout.

| Fresh inputs | Total inputs | Distinct labelled truth tables | Exact gate count |
|---:|---:|---:|---:|
| 0 | 5 | 30 | 8 |
| 1 | 6 | 360 | 9 |
| 2 | 7 | 3,780 | 10 |

There are 15 labellings of the five-input function and 15 of its dual. They have different numbers of true rows. Fixing any of their five inputs leaves a nonconstant function. This distinguishes a newly added outer input, which can be fixed to make the whole function constant. With one fresh input, six positions and two gate choices give 6 × 2 × 30 tables. With two fresh inputs and equal gate types, their order has no effect, giving 2 × 21 × 30 tables. With different gate types their order is recoverable, giving another 2 × 7 × 6 × 30. A Python enumeration constructs and deduplicates the full truth tables. [Enumeration](outer_gates.py) · [Tests](test_outer_gates.py)

The dual of the assigned function has a graph description. It holds when the outer input is true or when the selected vertices contain an edge of two triangles sharing a central vertex. Swapping two labels gives L-meta-13203. Lean verifies the graph identities, counts 180 distinct labelled tables in the assigned function’s permutation and duality orbit, and proves an exact nine-gate minimum for every member. The project had an earlier exact bound for this sibling. [Graph certificate](Butterfly.lean) · [Earlier exact bound](https://github.com/open-goat/pequalnp-proofs/pull/17408) · [Merged proof](https://github.com/open-goat/pequalnp-proofs/pull/17475)

## Replay

From this directory, with Python 3.9 or later, run the enumeration and tests.

```sh
python3 outer_gates.py 0xe8a8a800 5 1 --find 0xa880888088800000
python3 outer_gates.py 0xe8a8a800 5 2
python3 -m unittest test_outer_gates
```

For Lean, use upstream commit `80aac8d96bdf7dbaca7471308f4e7fbacbfe3098` with pinned Lean 4.36.0 and Mathlib. Set `research_dir` to this directory’s absolute path and `upstream` to the upstream checkout. From the upstream `lean/` directory, build the dependencies and check the research files.

```sh
cd "$upstream/lean"
lake build PEqualNP.Outside.L_meta_4795 PEqualNP.Outside.L_meta_8637 PEqualNP.Outside.L_meta_12184
replay_dir=$(mktemp -d)
lake env lean --root="$research_dir" -o "$replay_dir/FreshOutput.olean" "$research_dir/FreshOutput.lean" &&
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/OuterChain.lean"' sh "$replay_dir" "$research_dir"
lake env lean --root="$research_dir" -o "$replay_dir/ExactMinimum.olean" "$research_dir/ExactMinimum.lean" &&
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/Butterfly.lean"' sh "$replay_dir" "$research_dir"
```

For the official local verifier, use a fresh upstream checkout with its dependencies installed. The desk assigned the negation L-meta-15094, so the diagnostic proves its refutation.

```sh
cd "$upstream"
proof=lean/PEqualNP/Outside/L_meta_15094.lean
python3 "$research_dir/pack_refutation.py" "$upstream" "$proof" &&
  node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute
```

The official verifier run locally returned `ACCEPTED (refute)` on source SHA-256 `2cf642d79f781c99568678ba23538607c2d3f4ebae1c10c2f61b760060d047b4`. It rechecked 2,538 constants and listed only `propext`, `Quot.sound` and `Classical.choice`.
