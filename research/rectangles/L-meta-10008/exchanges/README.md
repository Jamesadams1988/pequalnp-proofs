# Exchanges around the 21-rectangle cover

For the matrix in L-meta-10008, any cover with at most 17 rectangles contains **at most 10** of the 21 specific rectangles in `donor_10011.json`. Exhaustive search tested all 116,280 ways to retain 14 donor rectangles. In every case the remaining zeros require at least seven further rectangles. If a cover of size at most 17 contained 11 donor rectangles, adding three more donor rectangles would give 14 retained boxes and at most six others.

This is a local obstruction. It leaves covers sharing ten or fewer donor boxes open. The conclusion uses exact equality of rectangles. The 21-rectangle upper bound comes from [L-meta-10011, darkmistofwoods](https://github.com/open-goat/pequalnp-proofs/commit/ad37304359fd4645873aa0b39326bdeda2f70b93). Its mask verifier credits [L-meta-10015, Mikael Pettersson](https://github.com/open-goat/pequalnp-proofs/commit/7d94d61ce8a900981cb357db8d91bbba41b96fc6). The local exchange computation takes the rectangles from the former proof. The Lean emitter adapts the finite mask checks used in both.

## Replay the exchange search

Run these commands in this directory with Python 3 and a C++20 compiler. The temporary directory keeps generated files outside the checkout.

```sh
scratch=$(mktemp -d)
python3 instance.py donor_10011.json > "$scratch/instance.txt"
c++ -std=c++20 -O3 exchange.cpp -o "$scratch/exchange"
"$scratch/exchange" 7 6 5000 < "$scratch/instance.txt"
```

A complete replay prints the following line.

```text
tested 116280, unresolved 0, nodes 25444118, largest 2701
```

The arguments specify the number of removed donor rectangles, the number of allowed replacements and a per-deletion search-node budget. A partial run reports the number of unresolved cases and exits with status 3. A positive run emits an explicit mask-pair witness on standard output. Completed negative and positive runs exit with status 0. The six-to-five run with arguments `6 5 10000` examined 54,264 deletion sets with zero unresolved, 1,368,878 search nodes and a maximum of 263 nodes.

For a fixed deletion set the vertices are the zero cells missed by the retained boxes. Two vertices are adjacent whenever one of their two cross-entries is a one. Every rectangle can cover only one independent set. Conversely, each independent set lies in the product of its rows and columns, and that product contains only zeros. Thus the remaining cells admit at most six rectangles exactly when the graph admits a six-coloring. The recursive search selects a vertex with the fewest available colors and branches over all allowed used labels plus the first unused label. A permutation of unused colors justifies the symmetry reduction. These exchange results were checked with the C++ search. The Lean file separately verifies the 21-rectangle control.

## Check or regenerate a Lean certificate

```sh
python3 make_certificate.py assignment.json donor_10011.json "$scratch/Control21.lean" \
  --name RectangleCover.control21
cmp Control21.lean "$scratch/Control21.lean"
```

From the project's configured `lean/` directory, run `lake env lean /absolute/path/to/Control21.lean`. The file imports `PEqualNP.Defs` and uses `decide +kernel` to verify all soundness and coverage conditions.

The emitter accepts a JSON array of rectangle pairs. Each component can be a decimal bitmask or a list of zero-based indices. Ordinary mode emits the actual number of supplied rectangles as an upper bound. With `--refute`, it requires a valid cover at or below the assignment's threshold and emits the literal negation of the assigned proposition. It rejects invalid masks, rectangles covering a one and uncovered zero cells before generating Lean. The fork contains the 21-rectangle control. A witness at threshold 17 remains open.
