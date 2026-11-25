# Six gates suffice with or without NOT

Research by James Adams (Jamesadams1988).

L-meta-13050 asks whether allowing NOT can save a gate for a particular six-input monotone function. For this function the minimum is **six** in both models. The Lean proof establishes monotone replacement at every gate budget. The companion exhaustive calculation establishes the exact minimum. [Desk statement](https://data.pequalnp.com/data/lemma/L-meta-13050.2206c70ff356.json) · [Lean proof](L_meta_13050.lean) · [Exact comparison](compare.py)

## A six-gate circuit

Number the inputs from 0 to 5. Splitting the table at its minimal true inputs gives the following expression.

```text
x0 OR ((x1 AND (x4 OR (x2 AND x5))) OR (x2 AND x3))
```

It contains six binary gates. Lean checks the expression on all 64 inputs. Each of the six input variables is essential, which means there is a pair of inputs differing only in that variable on which the result changes.

## A reusable replacement proof

Suppose a function of n essential inputs has an AND/OR circuit of size at most n. Then every fan-in-two AND/OR/NOT circuit for that function has an AND/OR replacement at the same budget. A binary gate can combine two previously separate groups of inputs. A NOT gate reads only its first operand and adds no dependency of its own. To bring n essential inputs to one output takes at least n − 1 binary gates. If a circuit also contains a NOT, it costs at least n and the given monotone circuit fits. A circuit made entirely of AND and OR serves as its own replacement.

The formal lemma `replace_at_n` covers zero-input gates, a second operand on a NOT, and the project's default false value for unavailable wires. Its support counting adapts KainanP's L-meta-757 proof and the project's support helpers. A separate positive-twin proof by k-sandhu uses a restriction argument. [KainanP's proof](https://github.com/open-goat/pequalnp-proofs/blob/073fb082aa04ea681e8529ca9f5bc67580e5ad4a/lean/PEqualNP/Outside/L_meta_757.lean) · [Support helpers](https://github.com/open-goat/pequalnp-proofs/blob/a22215b470de7d5779a9df8af2365c07e94e1fdf/lean/PEqualNP/MetaComplexity/Helpers/Support.lean) · [k-sandhu's PR](https://github.com/open-goat/pequalnp-proofs/pull/16553)

## Why five gates cannot suffice

Trace the output backwards to the inputs it can read. All six essential inputs must occur. With g reachable gates the connected graph needs at least g + 5 edges and can have at most 2g. If the entire circuit has at most five gates, equality forces a tree of five binary AND/OR gates with each input at exactly one leaf. The Python replay enumerates such trees by partitioning the variables between their two root subtrees and combining their truth tables. It finds 5,504 distinct six-variable functions and verifies that the target is absent.

## Replay

Run `python3 compare.py` from this folder with Python 3.10 or later. It checks the upper bound, the five-gate exclusion, and positive and negative controls.

For the Lean replay, use a prepared checkout of upstream commit `a22215b470de7d5779a9df8af2365c07e94e1fdf`, with its pinned Lean 4.36.0 and Mathlib. Set `research_dir` to this folder's absolute path, then run the commands below from the prepared repository root. The desk assigned the negative statement in prove mode. This local replay checks its refutation.

```sh
cp "$research_dir/L_meta_13050.lean" lean/PEqualNP/Outside/L_meta_13050.lean
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_13050.lean "$research_dir/Statement.txt" refute
```
