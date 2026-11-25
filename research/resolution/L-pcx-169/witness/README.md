# A 157-line ordinary-resolution refutation of PHP(5,4)

`Row169.refutation157` checks the locally constructed Hall derivation in `trace157.json`. It uses 5 pigeon axioms, 40 hole-collision axioms, and 112 resolutions. The JSON records positive and negative parents by their zero-based positions in chronological order. The pivot index is four times the pigeon number plus the hole number. L-pcx-169 asks for at most 149 lines.

`hall_seed.py` is the local derivation recipe. Upstream L-pcx-171 already contains a distinct 157-line certificate and states the bound 159. That certificate served as an independent control for the checker. [Upstream L-pcx-171](https://github.com/open-goat/pequalnp-proofs/blob/e4bb613e0d57717d4eeec4ac147030c55b6e7f3a/lean/PEqualNP/Outside/L_pcx_171.lean)

Prepare `PEqualNP.Defs` with `lake build PEqualNP.Defs` from the upstream `lean` directory at commit `e4bb613e0d57717d4eeec4ac147030c55b6e7f3a`. From this witness directory, run

```sh
./replay.sh path/to/upstream/lean
```

Replay checks the file hashes, regenerates `Hall157.lean` byte for byte, runs the standard Lean kernel on the regenerated source, and checks the reported axiom list. The result uses `propext`, `Classical.choice`, and `Quot.sound`.
