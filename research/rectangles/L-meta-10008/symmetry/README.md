# Symmetric rectangle covers of L-meta-10008

The prescribed matrix has an invariant cover of size 26 under one cyclic group of order 24, and an invariant cover of size 22 under a conic stabilizer of order 60. Both sizes are optimal for the specified group. A second cyclic group of order 20 requires at least 22 rectangles. The unrestricted 17-rectangle question remains open in these arguments.

Run `python3 verify.py` with Python 3.10 or later. The standalone verifier includes the matrix, paired permutations of its zero-based row and column indices, and orbit representatives for the two upper bounds. It checks that the permutations preserve every entry and expands each witness against all 961 entries.

## Cyclic groups

In projective coordinates over the field of five elements, `tor24` sends `(x,y,z)` to `(3y,x+y,z)`. The generator `j20` sends it to `(x+y,y,2z)`. The explicit index permutations specify the groups independently of the coordinate labeling.

Every cover must contain a rectangle at the zero entry (0,10). If a nontrivial subgroup stabilized this rectangle, some prime-order subgroup would stabilize it. The rectangle would contain the product of the subgroup orbits of row 0 and column 10. In the order-24 group the products for primes 2 and 3 contain the one entries (0,6) and (0,26), respectively. In the order-20 group the corresponding witnesses for primes 2 and 5 are (0,6) and (0,20). Consequently the rectangle has a full orbit.

Write the group order as *n*. A cover of size at most *n* + 1 consists of that orbit and at most one other rectangle. Both groups fix a row and a column. If any rectangle in the orbit contains the fixed row, all do. All rectangles in the orbit must then omit the six columns incident to that row. A single other rectangle cannot cover all zeros of two such columns, since their zero sets are distinct and each has 25 elements. Thus the full orbit omits the fixed row, and the extra rectangle must cover all 25 of its zeros. By the same argument with rows and columns exchanged, the extra rectangle must cover every zero of the fixed column. This is impossible because any rectangle containing all zeros of one row can contain only that row, while the fixed column has 25 zeros. The verifier checks these cardinality and distinctness properties directly. For the first cyclic group, orbits of sizes 24, 1, and 1 attain 26.

## The order-60 group

The named generators `s1101` and `s0411` come from the symmetric squares of the two-by-two matrices with rows (1,1),(0,1) and (0,4),(1,1), respectively. They act on the Veronese conic via the projective special linear group PSL(2,5). The indexed permutations suffice for the calculation.

Every nonempty all-zero rectangle can be enlarged canonically by taking every column disjoint from its row set and then every row disjoint from the resulting column set. The resulting rectangle is maximal. These enlargements commute with the group action because the permutations preserve the two sides. Removing empty rectangles and duplicate enlargements preserves coverage and can only reduce the orbit family's size.

For a cover of size at most 21, any rectangle has a nontrivial stabilizer because the full group has order 60. Its stabilizer contains a subgroup of order 2, 3, or 5. The verifier enumerates those cyclic subgroups up to conjugacy directly from the permutations. For each representative it enumerates every union of cycles of the row permutation, retaining distinct possible column intersections. Closing those sets and taking their full group orbits gives all possible maximal rectangles with orbit size at most 21. The result has 241 candidate rectangle orbits and 21 target orbits of zero entries.

The decision search chooses one uncovered target orbit and tries every candidate containing it whose cost fits the residual budget. Invariance ensures that a candidate containing one cell of a target orbit covers that entire orbit. A budget of 21 fails. The three explicit representatives in the verifier generate orbits of sizes 10, 6, and 6 and cover every zero.
