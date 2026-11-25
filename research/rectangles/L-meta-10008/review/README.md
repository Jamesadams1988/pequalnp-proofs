# Independent checks for L-meta-10008

The assignment asks whether the complement of the specified 31-by-31 incidence matrix needs at least 18 rectangles. The upstream snapshot at `41fe834b000fc5190f11224bb9e6bc645249cc7b` gives the interval **15 through 21**. The 15 lower bound uses the rectangle area bound and reflection in the span of the selected row vectors. The 21 upper bound has an explicit certificate. Independent cell-by-cell replay checks all four upstream covers in the table. [Lower bound, PR 17199](https://github.com/open-goat/pequalnp-proofs/pull/17199) · [Upper bound, PR 15942](https://github.com/open-goat/pequalnp-proofs/pull/15942)

| Checked upstream file | What its theorem proves | Rectangles in its certificate |
| --- | --- | ---: |
| [10002](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10002.lean) | At least 14 | |
| [10004](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10004.lean) | At least 15 | |
| [10011](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10011.lean) | At most 21 | 21 |
| [10013](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10013.lean) | At most 24 | 24 |
| [10015](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10015.lean) | At most 27 | 26 |
| [10017](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10017.lean) | At most 28 | 28 |

All six theorems use the exact list of rows in the assignment. A search of the snapshot for the 31-by-31 rectangle type found precisely these six files. The other fourteen files under `lean/PEqualNP/Outside` containing `Fin 31` state theorems about other objects. The public desk snapshot dated 2026-11-25 23:08 UTC listed both 10007 and 10008 as open. GitHub title searches on that date returned zero PRs for each of those IDs as well as the neighboring 15- and 19-rectangle questions.

## The largest fooling set has six cells

A fooling set consists of zero cells for which every two are incompatible with a common all-zero rectangle. Rows and columns in such a set are distinct. Suppose it contains seven cells and select their seven points and seven lines. Write $t_j$ for the number of selected points on the $j$-th selected line. Incompatibility forces at least one cross-incidence for each of the 21 pairs of cells. Therefore $\sum_j t_j\ge21$. A pair of distinct points has just one joining line, so $\sum_j \binom{t_j}{2}\le21$.

The integer inequality $\binom{t}{2}\ge3t-6$ holds for all nonnegative $t$, with equality exactly at 3 and 4. The two bounds imply $\sum_j t_j=21$ and equality in every term. Consequently each selected line contains exactly three selected points, and every pair of selected points is joined by a selected line. Each selected point lies on exactly three selected lines, since the six other points occur in pairs on those lines. Counting intersecting line pairs gives $7\binom{3}{2}=21$, so two selected lines always meet in a selected point.

Each of the seven selected lines contains three further points, all distinct across lines. These lines cover 28 of the plane's 31 points. From any uncovered point there are six lines to reach the seven selected points. Two selected points must share a joining line through the uncovered point. That line is selected, giving a contradiction. This is the order-five instance of Bruck's restriction on projective subplane orders. The argument uses only the incidence counts verified for this matrix. [Ostrom and Sherk, *Finite Projective Planes with Affine Subplanes*](https://doi.org/10.4153/CMB-1964-051-8)

The six zero-based cells `(8,25), (13,28), (16,12), (21,11), (18,20), (5,17)` attain the bound. Lean checks their 15 pairwise incompatibilities. The Python replay also enumerates all 15,500 quadrangles and finds zero with collinear diagonal points, an independent check that the plane contains no Fano subplane.

## Lean results for row supports

[TwoSupports.lean](TwoSupports.lean) checks that distinct points have a unique joining line and that one can choose a line through either point avoiding the other. It uses the exact matrix to prove the following implications for a list of sound rectangles that covers all nonincidences of a designated row.

- A sole supporting rectangle must have singleton row side.
- Given two nonsingleton supporting row sides containing the designated point, their intersection is exactly that point and their union lies on a line. Any two points of a nonsingleton support determine its carrier line uniquely.
- For any other row, some rectangle contains the designated row and omits the other row. Thus support codes indexed by positions in the original list are injective on covered rows, including those with two-element support codes.

The file also checks the six-cell witness. The seven-cell exclusion above and the full degree-profile count are written arguments. The five axiom reports at the end of the file contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Finite replay

From this directory, Python 3 verifies the incidence data, quadrangles and witness. Providing a clone containing the pinned upstream commit also checks the six public file hashes against the desk snapshot and replays each concrete cover.

```sh
python3 replay.py
python3 replay.py --upstream-git /path/to/pequalnp-proofs
```

`--cover FILE` additionally checks a JSON array of row/column lists, a JSON array of mask pairs, a text file of decimal mask pairs, or a package certificate with explicit rows, rectangles and missing cells. The output gives the exact number of invalid and uncovered cells and all positive coverage multiplicities.

The C++20 enumerator independently counts all **1,565,748** nonempty maximal zero rectangles. It generates sides in increasing order on each shore, closes them by incidence, and counts equal-width-and-height rectangles once. The upstream area bound 60 implies each rectangle has a shore with at most seven vertices, so the search through size seven is complete. Exactly 6,200 maximal rectangles have area 60.

```sh
c++ -O3 -std=c++20 maximal.cpp -o ./rectangle-maximal
python3 -B -c 'from replay import ROWS; print(*ROWS)' | ./rectangle-maximal
```

Run Lean from the upstream `lean/` directory with dependencies built at the pinned toolchain. Supply the absolute path to this file.

```sh
lake env lean /path/to/review/TwoSupports.lean
```
