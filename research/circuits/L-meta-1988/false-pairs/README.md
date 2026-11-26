# False-positive pairs at a terminal AND in PG(2,3)

Write P and Q for two monotone operands of a terminal AND satisfying the incidence and negative tests of L-meta-1988. For each operand, form the family of two-vertex nonedges it accepts. A mixed pair has a point and a nonincident line. There are 117 mixed nonedges and 273 nonedges of all types.

| Families counted | Largest smaller family | Largest sum | Largest product |
|---|---:|---:|---:|
| Mixed false-positive pairs in each operand | 12 | 61 | 324 |
| All false-positive pairs in each operand | 30 | 145 | 1,638 |

Each entry is a separate sharp maximum when both families in the indicated row are nonempty. The smaller-family and product bounds still hold if one is empty, with value zero in that case. Allowing an empty family raises the sharp sum to 117 for mixed pairs or 273 for all pairs. Take one operand to be the incidence edge function and the other to be constantly true to attain these sums. For example, one operand can accept all 21 nonedges through a fixed point, while the other accepts all 78 nonedges having an endpoint among the four lines through that point. This attains the product 1,638. For a 30-by-41 example, choose two lines through that point. Add to the first family the nine pairs consisting of one other point on each line, and take all nonedges meeting either line as the second family.

One operand always accepts at most 12 mixed false positives. It therefore accepts at most one singleton. Each accepted singleton forces nine mixed false positives, and the sets contributed by two distinct singletons overlap in at most one pair. At least 48 of the 52 incidence pairs are consequently minimal true inputs for this operand. It depends on every vertex v, since at least three of the four incident neighbors w have a false singleton while the pair {v,w} is true. This essentiality statement also follows from a short argument independent of the enumeration. Every accepted singleton of one operand must be incident to every accepted singleton of the other, because a nonincident union extends to a prescribed negative test. Two distinct singleton supports on both sides would therefore give a 4-cycle. The incidence graph has no 4-cycle.

## Why the terminal tests impose compatibility

Let e be a false positive of the first operand and f one of the second. If their union contains no incidence, its smaller side has size at most two because the union has at most four vertices. Keep that smaller side and add every opposite-side vertex avoiding it. This gives one of the prescribed negative tests. Monotonicity makes both operands true on that test, a contradiction. Thus some endpoint of e is incident to some endpoint of f. Call this compatibility. The reasoning applies regardless of other minterms or shared internal gates.

Conversely, take two nonempty families with every cross pair compatible. The edge functions of the incidence graph augmented by each family are monotone operands whose conjunction equals the original edge function on every input. A common false positive would contain an edge from each family and therefore contain an incidence. Thus the graph extremal problem gives sharp pair-level constraints. These constraints alone do not establish a circuit-size lower bound of 63.

## Replay

Compile and run with C++20. No external data are required.

```sh
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
c++ -O3 -march=native -std=c++20 verify.cpp -o "$build_dir/verify"
"$build_dir/verify"
```

The program constructs the incidence relation from the four residues 0, 1, 3 and 9 modulo 13. Vertices 0 through 12 are points, and vertices 13 through 25 are lines. Fix an anchor e in the first family and restrict possible columns to nonedges compatible with e. Intersecting the neighborhoods of all selected rows produces a maximal column family for those rows. Conversely every such intersection is reachable by successively adding rows. Counting all rows covering that intersection gives a valid rectangle containing the anchor. Maximizing over these rectangles finds the three coordinatewise extrema.

The shifts p ↦ p+t, l ↦ l−t, simultaneous multiplication by 3, and point–line exchange preserve incidence. They split mixed pairs into three orbits, represented by (0,15), (0,17), (0,20), since the possible point-plus-line residues range over the multiplicative orbits of 2, 4 and 7. Unordered same-side pairs have two orbits represented by (0,1) and (0,2), using multiplication by 3, endpoint exchange, and point–line exchange.

The mixed-only sweep retains every nonempty column intersection. For the unrestricted sum and product, transpose any rectangle with a side of size at least 41 to use that side as columns. All five anchor orbits are checked at threshold 41 or lower. If both sides have size at most 40, their sum is at most 80 and their product at most 1,600. For the unrestricted smaller-side maximum, any rectangle of size at least 31 by 31 containing a mixed pair has a mixed anchor after a possible transpose. The three mixed-anchor sweeps at threshold 31 exclude this case. If neither family has a mixed pair, compatibility and nonemptiness force the families to consist entirely of point-pairs and line-pairs on opposite sides. The final direct recursion excludes 31 by 31 for each of their two anchor orbits.
