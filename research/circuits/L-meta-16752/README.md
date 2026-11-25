# Nine gates for a family of six-input Boolean functions

James Adams (Jamesadams1988) used two input restrictions to prove nine-gate lower bounds for 87 truth tables in the November 25, 2026 public desk export. For each table the Lean theorem covers every fan-in-two AND/OR/NOT circuit, including circuits that reuse gates. **For 50 of the 87 functions, Lean also verified a nine-gate monotone circuit, establishing the exact unrestricted and monotone minimum.** The table manifest contains positive row IDs so another contributor can find the certificate for a particular function. [Manifest](thresholds/rows.tsv) · [87 Lean lower bounds](thresholds/ThresholdBatch.lean) · [Proof generator](thresholds/generate.py) · [Kernel verification](thresholds/verification.json)

## How the lower bound works

Choose an essential input and fix its value. If the resulting function is nonconstant, gate elimination saves at least one gate. Choose an input that is still essential after that first restriction and repeat. For 57 functions this leaves the four-input two-of-four threshold. For 30 it leaves three-of-four, its De Morgan dual. The library gives a seven-gate lower bound for two-of-four and proves that dualization preserves the budget here. Combining the two savings gives nine. The generator emits the essentiality witnesses and verifies the complete truth table at each restriction. [Earlier gate-elimination research](../L-meta-13646/CofactorBound.lean) · [Upstream threshold bound and dualization](https://github.com/open-goat/pequalnp-proofs/blob/24da7e46a0e459042fabd6d250b9503af98bbd57/lean/PEqualNP/Outside/L_meta_12184.lean)

The census used the public export generated at 20:41:21 UTC, SHA-256 `76238e0dee3c297410e6cf9b49670aa83f92955dccbbaa3f9b533feffd3b70f2`. It scanned 842 distinct six-input tables in the positive fixed-statement replacement format with a split 64-bit literal. A separate enumeration reproduced all 87 matches. The manifest supplies all literals needed to replay the proofs after the live desk changes. [Export](https://data.pequalnp.com/data/desk/gaps.json) · [Manifest extractor](thresholds/manifest.py)

## Which functions attain nine gates?

An exhaustive native search through monotone formula trees with at most nine gates found a witness for 50 tables. Lean independently evaluated each circuit on all 64 rows and paired it with the unrestricted lower bound. For the other 37 tables the search excludes monotone trees of that size. A nine-gate circuit that reuses an intermediate result is still possible. The witness file gives the expression and depth for each success. [Witnesses by row](family/family.tsv) · [50 exact Lean proofs](family/FamilyExact.lean) · [Proof generator](family/generate_exact.py) · [Tree search](family/trees.cpp)

## The assigned table

For L-meta-16752 the literal is `0xfeeaeeeafeeaeaaa`. Fix input 0 to false and then original input 5 to false. The four remaining inputs compute three-of-four. A nine-gate monotone circuit attains the lower bound, so the posted claim that negations can save a gate on this table is false. The official checker, run locally in diagnostic refutation mode, returned `ACCEPTED (refute)` for source SHA-256 `32a810574e4160bb8c9a1136e08415167318ae84db009b2568b0f763ad13224e`. It rechecked 2,051 constants. The original positive submissions by azizsayadi1155 and Leg0shii predate this research. The nine-gate witness here extends a circuit already published in L-meta-1423. [Lean proof](Threshold.lean) · [Five-input witness](https://github.com/open-goat/pequalnp-proofs/blob/24da7e46a0e459042fabd6d250b9503af98bbd57/lean/PEqualNP/Outside/L_meta_1423.lean) · [PR #21184](https://github.com/open-goat/pequalnp-proofs/pull/21184) · [PR #21234](https://github.com/open-goat/pequalnp-proofs/pull/21234)

There is also a shorter proof of the same-budget replacement statement. The function has the form `x0 OR g`, and upstream L-meta-8642 supplies the five-input theorem for exactly `g`. The general transfer allows the added AND or OR input at any position and proves that its cost is one gate for every nonconstant core. [General transfer](FreshOutputAt.lean) · [Worked example](Row16752Example.lean) · [Five-input donor](https://github.com/open-goat/pequalnp-proofs/blob/24da7e46a0e459042fabd6d250b9503af98bbd57/lean/PEqualNP/Outside/L_meta_8642.lean)

Two independent finite searches gave a minimum of ten literal leaves for a formula tree, even with free negations at leaves. The displayed formula computes all 64 outputs. Lean also checks an integer threshold representation with weights (8, 4, 3, 3, 2, 1) and threshold 8, and proves that these coordinates and threshold are componentwise least among nonnegative integer representations. [Formula replay](finite/README.md) · [Independent formula search](finite/formula_control.cpp) · [Threshold proof](ThresholdWeights.lean)

## Reproduce the results

Use this research checkout and an upstream checkout at `24da7e46a0e459042fabd6d250b9503af98bbd57` with the project's pinned Lean 4.36.0 and Mathlib installed. From this directory, run the following commands with the paths to those checkouts.

```sh
bash replay.sh /path/to/upstream/lean
python3 family/tree_replay.py > /tmp/row16752-trees.tsv
cmp family/family.tsv /tmp/row16752-trees.tsv
python3 finite/circuit_check.py
python3 finite/formula_check.py
c++ -std=c++20 -O2 finite/formula_control.cpp -o /tmp/row16752-formula-control
/tmp/row16752-formula-control
```

To reproduce the single-file diagnostic, run these commands with a fresh upstream checkout that has its dependencies installed. The file generator verifies its input hashes and requires a new output path.

```sh
research_dir="$PWD"
cd /path/to/upstream
proof=lean/PEqualNP/Outside/L_meta_16752.lean
python3 "$research_dir/pack_refutation.py" "$PWD" "$proof" &&
  node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute
```
