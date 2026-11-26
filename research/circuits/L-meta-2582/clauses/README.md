# Raw monotone CNFs for projective-plane incidence

For the Desarguesian planes PG(2,2), PG(2,3), and PG(2,4), the minimum number of clauses in a monotone CNF for full point-line incidence is **37**, **704**, and **25,237**, respectively. Each clause is a disjunction of original positive point and line variables.

| Order | Variables | Minimum clauses | Clause width and multiplicity |
|---:|---:|---:|---|
| 2 | 14 | 37 | 7 × 2, 9 × 14, 10 × 21 |
| 3 | 26 | 704 | 13 × 2, 16 × 26, 18 × 156, 19 × 468, 20 × 52 |
| 4 | 42 | 25,237 | 21 × 2, 25 × 42, 28 × 420, 30 × 2,408, 31 × 5,460, 32 × 16,800, 34 × 105 |

A true assignment contains both endpoints of an incidence edge. The true variables of a maximal false assignment therefore form a maximal independent set in the incidence graph. Its complement is a minimal vertex cover. Every clause in a correct monotone CNF must hit every edge, since the two endpoints of any edge alone satisfy the function. A maximal false assignment must falsify at least one clause, whose variables then lie inside its complementary minimal cover. The cover's minimality forces that clause to equal the whole cover. Conversely, taking all these clauses computes incidence: each edge hits every clause, and every false assignment lies inside a maximal false assignment. This proves the exact clause count.

Write Γ(S) for the lines incident with at least one point of S. For each distinct union U of point neighborhoods, take all points P whose neighborhoods lie inside U and all lines outside U. Since U is the union of neighborhoods of points already in P, Γ(P) equals U. Every line omitted from this independent set touches P, and every omitted point touches a selected line, so the set is maximal. Conversely, maximality forces these two choices for every maximal independent set, recovering U uniquely.

Run `python3 -B clauses.py` with the sibling `packed/packed.py` in place. Starting with the empty union, the script adjoins each point neighborhood to every union obtained so far. It verifies Γ(P) = U for every union. For orders 2 and 3 it also enumerates all point subsets directly and compares the complete sets of maximal assignments. For order 2 it independently checks all 16,384 truth assignments. These counts concern clauses on the raw variables. Shared intermediate gates in an AND/OR circuit fall outside the bound.
