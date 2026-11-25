# An essential input split costs exactly one gate

Research by James Adams (Jamesadams1988).

L-meta-12578 asks whether NOT gates can make a circuit smaller for the six-input truth table `0xeeeaeae8eae8eae8`. The minimum is **nine gates** both with and without NOT. This table is an instance of a more general result about splitting one input into two. [Desk statement](https://pequalnp.com/desk/step?gap=L-meta-12578) · [Lean theorem](SplitTransfer.lean) · [Finite certificates](finite/README.md)

## The gate cost of splitting an input

Start with any Boolean function and choose an essential input, meaning that flipping it can change the output. Replace every use of that input by its AND with a fresh input. For circuits of fan-in at most two over AND, OR and NOT, this operation increases minimum size by **exactly one gate**. Other inputs can be inessential. If the original function has a monotone implementation at every feasible unrestricted budget, the new function inherits that property. [General proof](SplitTransfer.lean)

One new AND supplies the upper bound. For the lower bound, set the fresh input to true. This recovers the original function. The fresh input is essential before restriction, and the function still depends on the original essential input afterward. The project's gate-elimination theorem therefore saves at least one gate. These two constructions yield both directions of the size comparison, including the smallest budgets. [Upstream gate elimination](https://github.com/open-goat/pequalnp-proofs/blob/60be64c28412eaf170ca324320dcefd2a44d0346/lean/PEqualNP/MetaComplexity/Helpers/Elim.lean) · [Upstream wire relabeling](https://github.com/open-goat/pequalnp-proofs/blob/60be64c28412eaf170ca324320dcefd2a44d0346/lean/PEqualNP/MetaComplexity/Helpers/PermInputs.lean)

## The six-input calculation

The five-input core has table `0xeeeaeae8`. Replace input 4 by the conjunction of inputs 4 and 5. Lean checks that the resulting function agrees with the assigned six-input table and that input 4 is essential. Julleht's upstream L-meta-8683 already gives a monotone replacement at every feasible budget for the core. Applying the general theorem gives that replacement for the six-input function. A separate proof follows the same restriction directly and reproduces the literal logical opposite of the desk statement. [Application](SplitAudit.lean) · [Literal statement](ExactAudit.lean) · [Julleht’s merged proof](https://github.com/open-goat/pequalnp-proofs/pull/12865)

For the numerical minimum, the included monotone witness matches every one of the 64 possible inputs. The finite replay establishes the matching lower bound. All five core inputs are essential, so at least four binary gates are needed to connect them to one output. Four SAT instances exclude unrestricted circuits of sizes four through seven. Lean's standard LRAT checker verifies each UNSAT certificate, and a size-eight positive control reconstructs a circuit matching every core input. The one-gate shift then gives the six-input minimum of nine. [Circuit witness](Witness.lean) · [Encoding assumptions, positive control and replay](finite/README.md)

## Replay

Use the upstream checkout at `60be64c28412eaf170ca324320dcefd2a44d0346`, with its Mathlib cache installed and Lean 4.36.0 on PATH. From this directory, run the following. The first command checks the five research modules in a temporary directory. The second rebuilds and checks the finite certificates using CaDiCaL and Lean. [Pinned project configuration](https://github.com/open-goat/pequalnp-proofs/blob/60be64c28412eaf170ca324320dcefd2a44d0346/lean/lakefile.toml)

```sh
bash check_lean.sh /path/to/pequalnp-proofs/lean
python3 finite/verify.py --output /tmp/12578-replay
```

Three contributors also posted proofs of the positive statement L-meta-12577. We independently replayed TSGut's proposed proof with the official local checker in refutation mode. Upstream adjudicates those PRs separately. [evgeth’s PR](https://github.com/open-goat/pequalnp-proofs/pull/16940) · [nicohabets’s PR](https://github.com/open-goat/pequalnp-proofs/pull/17135) · [TSGut’s PR](https://github.com/open-goat/pequalnp-proofs/pull/17564)

## Replay the official local checker

The generator reproduces the structural proof as a single Lean file importing only `PEqualNP.Defs`. It draws the five-input proof from Julleht's L-meta-8683 and the pinned restriction and relabeling helpers from k-sandhu's L-meta-12433. The upstream credits stay in the generated file. [Generator](pack.py) · [Assigned statement](statement.txt) · [k-sandhu's merged proof](https://github.com/open-goat/pequalnp-proofs/pull/16510)

From this research directory, set `upstream` to a separate checkout of the pinned revision with Lean, elan and the project cache configured. The following creates the research input at the path expected by the checker, then checks the logical opposite of the assigned statement.

```sh
research_dir=$PWD
upstream=/path/to/pequalnp-proofs
proof=lean/PEqualNP/Outside/L_meta_12578.lean
test ! -e "$upstream/$proof" &&
  python3 pack.py "$upstream" Structure.lean statement.txt "$upstream/$proof" &&
  (cd "$upstream" && node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute)
```

On the pinned checkout, the official local checker returned `ACCEPTED (refute)` for the generated input with SHA-256 `47a385d97b270ba54737704a118db0b2d629ba38b65d77f118e4d814c0a2131a`. It rechecked 2,002 constants and reported only `propext`, `Quot.sound` and `Classical.choice`.
