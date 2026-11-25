# The ten-rectangle cover for L-meta-9294

James Adams (Jamesadams1988)

This 10-by-10 binary matrix has 60 one-entries. Ten all-one rectangles cover them, and nine cannot. The upstream intake checker accepted kinduff’s proof of the nine-rectangle lower bound in the opposite row, L-meta-9298, on November 25, 2026. The receipt names the same commit that was at the head of the open PR when this replay was made. [Upstream proof and verdict](https://github.com/open-goat/pequalnp-proofs/pull/13353#issuecomment-7160922377)

[TenRectangles.lean](TenRectangles.lean) proves the ten-rectangle upper bound against the row masks in the desk statement. [cover.py](cover.py) independently finds a minimum cover. It also computes the largest fooling set, a set of one-entries of which no two can lie in a single all-one rectangle. Its maximum size here is seven. The coordinates and ten row-mask/column-mask pairs are in [answer.json](answer.json). Coordinates start at zero, with column zero in the least significant bit.

## Replay

From this directory with Python 3.10 or later, run the following command. An empty diff reproduces the saved report.

```sh
python3 cover.py | diff -u answer.json -
```

From the project's configured `lean/` directory, run `lake env lean /path/to/TenRectangles.lean` using Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

## Why the search is exhaustive

Every nonempty all-one rectangle can be enlarged to a maximal one. Intersect the one-columns of its rows, then add every row containing all those columns. Enumerating these intersections produces 110 distinct maximal rectangles, 80 of area six and 30 of area eight.

For each budget the search selects an uncovered cell and branches on every viable maximal rectangle containing it. It discards a state when even the sum of the largest available gains falls short. It discards an individual choice when the other rectangles, even at their maximum area, could not finish the cover. Eight and nine rectangles fail. The ten-rectangle witness reproduces all 100 entries by direct comparison. A separate clique search computes the fooling-set maximum in the graph of incompatible one-entries.
