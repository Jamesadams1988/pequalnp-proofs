# Reproduce the zero-pivot proof

The modular build compiles the proof of L-meta-17103 from upstream commit `6284ae5ebdec19cb4bce06d15e190de3560bc099`. It preserves every declaration body, including each original `decide +kernel` certificate. The generator splits the source into 87 ordinary `PEqualNP.Outside.Split17103` modules at declaration or section boundaries. A final wrapper exposes the upstream theorem name. The generator also reassembles the original bytes from the split files and checks the pinned SHA-256 digest.

From any directory, provide absolute paths to this research package and the pinned upstream checkout’s Lean directory. The output directory can be reused by subsequent verification runs.

```bash
package=/absolute/path/to/research/circuits/L-meta-11021
project=/absolute/path/to/pequalnp-proofs/lean
pivot=$(mktemp -d)
bash "$package/lower/split17103/build.sh" "$project" "$pivot"
```

The full `--prebuilt` replay also needs the other ten upstream declarations and the Shannon helper on its Lean search path. If they still need building, the following loop builds one case at a time.

```bash
(
  cd "$project"
  lake build +PEqualNP.MetaComplexity.Helpers.Shannon
  for n in 534 17107 17269 17271 17273 17275 17277 17279 17281 17283; do
    lake build "+PEqualNP.Outside.L_meta_$n"
  done
)
LEAN_PATH="$pivot${LEAN_PATH:+:$LEAN_PATH}" bash "$package/replay-lean.sh" "$project" --prebuilt
```

The split replay observed exit code 0 for all 87 parts and the wrapper. Parts P000–P058 used `-j1 -M 6000`. The remaining parts and wrapper used `-j1 -M 8000 -DElab.async=false`. The largest sample, from P068, was 3,494 MiB private and 6,164 MiB resident memory. Importing the resulting wrapper reported `propext`, `Classical.choice`, and `Quot.sound`. The final package replay separately runs the project's verifier on the assigned theorem. [Observed split-build data](observed.json) · [Package replay](../../replay-lean.sh)
