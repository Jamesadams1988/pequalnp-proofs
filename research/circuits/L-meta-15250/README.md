# Fifteen eight-gate functions from one seven-gate circuit

James Adams (Jamesadams1988) checked what happens when one operand of Scott Hazlitt’s five-input circuit for L-meta-8650 is combined with a fresh input. There are seven gates, two operand positions per gate, and two choices of inserted gate, AND or OR. The 28 edits give **15 distinct labelled functions**. Each requires eight gates even when NOT is allowed. Only one edit gives the table shared by L-meta-15249 and L-meta-15250. At the first gate, replace the right operand of `x1 OR x2` with `x2 AND x5`. These counts cover edits to this particular circuit. [Original seven-gate circuit](https://github.com/open-goat/pequalnp-proofs/pull/12798) · [Lean proof of the 28 minima](EdgeExtensions.lean) · [Enumeration](edge_extensions.py)

For each edit, fixing the new input to the neutral value of the inserted gate recovers the five-input function. Lean checks that the new input is essential for every edit. Gate elimination therefore saves at least one gate when the input is fixed. The recovered function already needs seven, and each edited circuit uses exactly eight. The argument uses Nico Habets’s gate-elimination proof, which credits sanchan. [Gate elimination](https://github.com/open-goat/pequalnp-proofs/pull/9322) · [Earlier construction](https://github.com/open-goat/pequalnp-proofs/pull/1992)

## All twelve restrictions of the assigned function

Fix an input of `0xeaa8c080ea88c080` to the indicated Boolean value and keep the other five in their original order. Each entry is the exact minimum in both the unrestricted fan-in-two AND/OR/NOT model and its monotone AND/OR submodel. Lean verifies a monotone circuit at every upper bound and instantiates Noptus’s exhaustive search for every lower bound. [Complete Lean certificate](CofactorProfile.lean) · [Noptus’s search](https://github.com/open-goat/pequalnp-proofs/pull/12814)

| Fixed input | False | True |
|---|---:|---:|
| x0 | 2 | 6 |
| x1 | 4 | 4 |
| x2 | 3 | 6 |
| x3 | 6 | 3 |
| x4 | 3 | **7** |
| x5 | 6 | **7** |

Fixing x5 to true gives Hazlitt’s literal table `0xeaa8c080`. Rows 21 and 53 witness that x5 is essential. Fixing x4 to true gives a second sharp lower bound from `0xeaa8ea88`. Earlier public submissions already imply the eight-gate optimum for the full function. edisonhello supplied an eight-gate witness and Leg0shii proved an unrestricted lower bound of eight non-NOT gates. The proof here uses a single restriction. [Single-restriction proof](ExactMinimum.lean) · [edisonhello’s PR](https://github.com/open-goat/pequalnp-proofs/pull/20398) · [Leg0shii’s PR](https://github.com/open-goat/pequalnp-proofs/pull/20464)

Complementing all inputs and the output and permuting the six coordinates gives the table for L-meta-13081. The companion proof checks this identity on all 64 rows and transports the eight-gate construction by exchanging AND and OR. Miguel Torres Perez’s merged proof supplies the lower bound. Nico Habets had already exhibited an eight-gate circuit for this companion. [Duality certificate](DualMinimum.lean) · [Merged lower bound](https://github.com/open-goat/pequalnp-proofs/pull/17264) · [Earlier optimal witness](https://github.com/open-goat/pequalnp-proofs/pull/18534)

## Reproduce the checks

With Python 3.9 or later, run these commands from this directory.

```sh
python3 edge_extensions.py
python3 ../L-meta-13646/cofactor_profile.py 0xeaa8c080ea88c080
```

For the four research certificates, use the upstream checkout at `96bf4611dda2eff096308b5c2587464a7092e902` with its pinned Lean 4.36.0 and Mathlib. Set `research_dir` to this directory’s absolute path. From the upstream `lean/` directory run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_4795 PEqualNP.Outside.L_meta_8650 PEqualNP.Outside.L_meta_8657 PEqualNP.Outside.L_meta_13081
for certificate in ExactMinimum EdgeExtensions CofactorProfile DualMinimum; do
  lake env lean "$research_dir/$certificate.lean" || exit 1
done
```

The official local checker returned `ACCEPTED (check)` for the positive L-meta-15249 and `ACCEPTED (refute)` for the assigned negative L-meta-15250. Each manifest names only its own proof file. Each run rechecked 2,065 constants and reported `propext`, `Quot.sound` and `Classical.choice`. From a fresh upstream checkout with the pinned dependencies installed, reproduce both checks with these commands. The generator requires new output paths and checks its source dependencies by SHA-256.

```sh
pos=lean/PEqualNP/Outside/L_meta_15249.lean
neg=lean/PEqualNP/Outside/L_meta_15250.lean
python3 "$research_dir/pack_proof.py" . "$pos" &&
  node tools/check-lean.mjs "$pos" "$research_dir/positive-statement.txt" check
python3 "$research_dir/pack_proof.py" . "$neg" &&
  node tools/check-lean.mjs "$neg" "$research_dir/statement.txt" refute
```

| Generated file | Source SHA-256 |
|---|---|
| L_meta_15249.lean | `7921f3e4b1d5a2747e0ec04a2c9e2dfff9a761e805943a395aee129ad54f29fd` |
| L_meta_15250.lean | `74111604c0276d82af80b64acd202624c0c5ba3cab5abbc361a8eb0aba221d54` |
