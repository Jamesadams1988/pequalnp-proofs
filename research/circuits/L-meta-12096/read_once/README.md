# An exact zero-extra solver for the signed circuit search

At zero extra budget, every remaining gate consumes two live positions and retains neither operand. The resulting computation is a read-once binary formula in those positions, with free input and output signs. The positions may carry identical, complementary, constant, or correlated functions of the six original inputs. Each position must occur exactly once in the expression. The tests use all 64 physical assignments, including when several coincide after projection onto a subset of positions.

The solver asks whether such a formula can be true on required-positive rows P and false on required-negative rows N. Other rows are unconstrained. On a single position it checks both signs. At an internal root, orient the output as AND or NAND, swapping P and N for NAND. Split the positions into two nonempty disjoint subsets A and B. For the smaller subset A, enumerate its exact signed read-once table values U by subset dynamic programming. For every U true on all required-positive rows, test the other subset recursively with the same positive rows and negative rows N intersected with U. This gives both directions: every actual formula selects such a split and such a U, and a successful right-side formula combines with U to realize the required labels.

Two necessary checks save work. Within the current subset, opposite required labels cannot share a projection. For a proposed root AND, a negative point cannot share its left projection with some positive point and its right projection with some positive point. The solver also checks the NAND orientation. Empty required-positive or required-negative sets are allowed. Leaf and subset enumeration still require actual realizable signed functions; constants enter only when the supplied leaves and their combination realize them on the physical rows.

## Reproduce

Run `python3 replay.py --all` with Python 3 and a C++20 compiler named `g++`. Omit `--all` for child 17 and the controls alone. Supply `--frontier /path/to/SignedFrontier.lean` to check the exact donor input words. The default also looks for that file in the parent directory and its `search` subdirectory. The standalone row fixture `rows.txt` contains the 256 row positions decoded from those six words, first the 128 negative rows and then the 128 positive rows. The replay checks their labels and coverage. `profile.cpp` performs the donor’s ordered transition rules at positive extra budget, using sorted multiset keys for memoization, and calls `read_once.hpp` at the first zero-extra bank.

| Measurement | Head 13, child 17 | Entire head 13 |
|---|---:|---:|
| Original raw donor calls | 471,208 | 122,486,249 |
| Raw calls with exact zero-extra cut | 65,930 | 10,144,859 |
| Raw zero-extra entries | 60,610 | 9,152,776 |
| Distinct zero-extra banks | 12,053 | 434,316 |
| Infeasible distinct banks | 12,053 | 434,316 |
| Distinct banks surviving the top rectangle check | 4,009 | 263,453 |
| Partial-label calls including top-level calls | 12,873 | 662,524 |
| Recursive smaller-side trials | 820 | 228,208 |
| Maximum recursion depth, top at zero | 1 | 2 |
| Measured native runtime | 0.30 s | 15.0 s |

A raw call is counted each time its position occurs in the donor’s recursion. A distinct bank is an exact multiset of wire functions, so duplicate positions are preserved. Partial-label calls include repeated residuals and both output polarities. All 118 head-13 children were infeasible. These are native C++ results. The equivalent Lean reflection for the full family of zero-extra banks remains a proof obligation.

`controls.cpp` independently enumerates gate merge orders and compares its result on 786 deterministic partial and total labelings, including correlated, duplicate, complemented and constant wires. There were 393 feasible and 393 infeasible examples. `borderline.py` gives a separate Python replay for the specific reachable ordered bank in `borderline.json`. Of its 62 root cut orientations only the AND whose left side is the first singleton survives the rectangle check. Only its positive literal covers the 26 positive rows. The right residual has 22 forced-negative rows and rejects all 30 root cut orientations. The source of the signed transition model is the case’s `SignedFrontier.lean`, adapted from upstream L-meta-14930.
