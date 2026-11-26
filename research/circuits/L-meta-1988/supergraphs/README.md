# Two strictly larger edge predicates for the order-three plane

Suppose the first factor is formed by partitioning the points and replacing every row in a block with the union of that block's original neighborhoods. Allow the second factor to add arbitrary nonedges. Exactly **93,002 ordered pairs** of strictly larger factors of this form have conjunction equal to incidence on every assignment. This counts labeled graphs with the row-coalescing graph designated as the first factor. Circuit minimization over those pairs remains open.

Let E be incidence, N(p) its row neighborhoods and E₁,E₂ the supergraphs. Every false positive would have to activate an extra edge (p,l) of E₁ and an extra edge (s,m) of E₂. The four endpoints themselves are a counterexample precisely when both crossed pairs (p,m) and (s,l) are nonedges. Thus the all-input check reduces exactly to testing opposite extra edges.

If p and q merge in E₁, row p gains the three lines in N(q) outside N(p), and row q gains the three in N(p) outside N(q). Any extra edge (s,m) in E₂ must have s distinct from p and q, since opposite extras in the same row fail the four-endpoint test. If m were outside N(p), all three new lines in row p would have to belong to N(s). They belong to N(q), and two lines have a unique common point. Hence s would equal q, a contradiction. The same argument forces m into N(q). This leaves just the unique common line of p and q.

It follows that if both factors are strictly larger, all merged pairs of the first factor have the same common line. All nonsingleton blocks belong to its four points. Conversely every partition of those four points works with every nonempty subset of the nine nonedges in that line's column as extras in the other factor. There are 13 lines, 14 nontrivial partitions of four labeled points and 511 nonempty choices of extras. The replay verifies every pair of original point-stars and all 182 distinct potential first factors against all 117 nonedges.

**An explicit 70-gate prefix.** In the zero-based labels of the desk, first merge points 0 and 1, whose common line is 0. The second factor instead adds just the nonedge (2,0). Form each point's original four-line OR (39 gates total). Form the eleven other point-stars and their combined OR R (21 more gates). Build the merged term (x₀ OR x₁) AND (N(0) OR N(1)) and combine it with R (four gates). For the other factor, form the original stars of 0 and 1 and the extra (2,0) term, and OR these with R (six gates). Both supergraphs are strict. The first has 58 edges and the second 53. Each described term is a bipartite rectangle on its entire input domain; the two supergraphs pass the cross-edge check, so the final free AND computes incidence on every assignment.

The replay checks all 169 singleton-edge assignments for the constructed gates and verifies the exact all-input compatibility criterion for the two resulting edge predicates. It found no prefix with at most 63 gates. The census is exhaustive for graph compatibility in the stated coalescence family; it does not exclude a shorter circuit for any of its graph pairs.

```sh
python3 coalescence.py | diff - results.txt
```
