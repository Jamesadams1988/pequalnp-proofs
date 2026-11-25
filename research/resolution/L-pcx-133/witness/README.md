# A 149-line refutation of BPHP(5,2)

`Row133.refutation149` proves that the 5-pigeon, 4-hole binary pigeonhole formula has a resolution-over-linear-equations refutation of length at most 149. The trace contains 40 collision axioms and 109 resolution steps. L-pcx-133 asks for a bound of 127.

`Witness149.lean` imports only `PEqualNP.Defs`. It was checked against upstream commit `68d8de6866df4e70ba92793c839867835e87b145`. In that checkout’s `lean` directory, first run `lake build PEqualNP.Defs`. From this witness directory, run the following command with the relative path to the prepared upstream project.

```sh
./replay.sh path/to/upstream/lean
```

Replay verifies the packaged hashes, regenerates the Lean source byte for byte from `trace149.json` using `emit.py` and `Template.lean`, checks the theorem, and prints its kernel axioms. The JSON lists lines in chronological order. The generator checks the pivot and both parent indices at each resolution. The emitted proof constructs the official newest-first line list. Use `python3 emit.py --help` for all supported rule formats.
