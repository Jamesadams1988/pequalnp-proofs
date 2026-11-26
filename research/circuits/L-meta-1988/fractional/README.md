# Exact fractional cover for canonical read-once factors

The 704 maximal negative assignments of the order-three incidence graph are the points of a set-cover problem. Each canonical read-once factor supplies the set of maximal negatives it rejects. The fractional covering number is **343/5**, so the largest integer lower bound obtained by assigning nonnegative weights to these 704 tests and bounding the weight rejected per factor is **69**.

Order the maximal negatives by sizes 13, 10, 8, 7 and 6. The profile of a factor gives the number of rejected negatives at each of those sizes. Use the following four classes of factors, giving each member of a class the same rational mass.

| Class | Profile | Number of supports | Mass per support | Total class mass |
|---|---|---:|---:|---:|
| A | (2, 0, 0, 0, 0) | 1 | 1 | 1 |
| B | (0, 0, 4, 6, 0) | 234 | 1/12 | 39/2 |
| C | (0, 0, 0, 10, 0) | 234 | 3/20 | 351/10 |
| D | (0, 4, 6, 0, 4) | 26 | 1/2 | 13 |

| Negative size | Number of negatives | Members of A, B, C, D rejecting each negative | Cover mass per negative |
|---:|---:|---|---:|
| 13 | 2 | (1, 0, 0, 0) | 1 |
| 10 | 26 | (0, 0, 0, 4) | 2 |
| 8 | 156 | (0, 6, 0, 1) | 1 |
| 7 | 468 | (0, 3, 5, 0) | 1 |
| 6 | 52 | (0, 0, 0, 2) | 1 |

The verifier computes and compares the four membership counts separately for every negative. It derives maximal negative assignments from the four incidence residues 0, 1, 3 and 9. For a maximal negative I, the canonical factor with singleton support S rejects I exactly when S is disjoint from I and the remaining vertices outside I and S form an independent set. The verifier enumerates every such remaining set, then groups the resulting 4,363,558 cut–support pairs by S. The argument for this rejection criterion is in the [canonical factor derivation](../read-once/README.md).

For any nonnegative weighting normalized so that each factor rejects weight at most one, multiply each factor inequality by its mass in the table and sum. The coverage of every negative is at least one, so total test weight is at most 343/5. Conversely, weighting the five sizes by (5, 0, 1, 1, 1) gives total test weight 686 and maximum rejected weight 10. Dividing by 10 attains 343/5. This argument bounds the weighted counting method for canonical read-once factors. It leaves the exact integral covering number open.

## Replay

Run from this directory using a C++20 compiler. The verifier uses integer arithmetic throughout and requires no external data.

```sh
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
c++ -std=c++20 -O3 verify.cpp -o "$build_dir/verify"
"$build_dir/verify" > "$build_dir/output"
diff -u expected.txt "$build_dir/output"
```
