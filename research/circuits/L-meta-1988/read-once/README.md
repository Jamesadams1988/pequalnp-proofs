# At least 69 read-once formula factors for PG(2,3) incidence

Suppose the output is an AND of monotone formulas, each of which contains every raw input variable at most once. The same variable may occur in any number of different factors. This construction requires **at least 69 factors** and at least 68 binary gates to conjoin their values. The statement also applies when subexpressions are shared between factors and each individual factor still has a read-once formula. Here “read-once” refers to syntactic read-once formulas on raw variables. The result leaves open the general two-wire cut of L-meta-1988, whose operands may have arbitrary internal sharing.

## Why it suffices to check 26-bit singleton sets

Write G for the incidence graph. Since the conjunction accepts every edge, so does every factor. For such a factor f, let S be the vertices whose singleton assignment makes f true. Force all members of S to zero and simplify constants. The remaining formula is read-once and rejects all singletons. Its accepted vertex pairs form a disjoint union of complete bipartite graphs and isolated vertices.

This last claim follows by induction at the root. Simplify constant children first. A nonconstant monotone child rejects the empty assignment, and the two children have disjoint variable sets. At an OR root, neither child accepts a singleton, and the two accepted-pair graphs form a disjoint union. At an AND root, an accepted pair must contribute one input to each child, and each of those singleton inputs must make its child true. This gives one complete bipartite graph.

Each connected component of G−S that contains an edge lies inside one such complete bipartite graph. Along any path, its colors alternate between points and lines. Consequently f accepts every mixed pair in that component. Define a canonical factor for S by disjoining its singleton inputs and, for each nontrivial component of G−S, adding the product of the OR of its points and the OR of its lines. These disjoint variable sets make the canonical factor read-once. It accepts all incidence edges. Monotonicity implies its true assignments are a subset of those of f. Replacing a factor by its canonical version therefore preserves the target conjunction and can only increase the number of false assignments it detects.

## Which maximal false assignments a factor detects

A maximal false assignment I is a maximal independent set of G. The canonical factor for S rejects I exactly when S and I are disjoint and the remaining vertex set T = V ∖ (I ∪ S) is independent.

If T is independent, every edge of G−S joins I to T. In each nontrivial connected component this bipartition agrees with the point–line bipartition, up to swapping, so its selected vertices in I all lie on one side. Conversely, if T contains an edge uv, each of u and v has a neighbor in I by maximality of I. Those two neighbors have opposite colors and lie in the same component of G−S. The canonical factor accepts their pair.

The promised negative tests include every maximal independent set here. For four points their four neighborhoods have union size at least 4·4 − 6 = 10, since each pair shares one line. At most three lines avoid those points, so every independent set has at most three members on one side. In a maximal independent set, its other side is precisely the set of all vertices avoiding this smaller side.

There is also a four-variable check of the necessary direction. For an edge uv inside T, let its two neighbors in I be the endpoints of the path through u and v. Restrict all variables outside that path to zero. The read-once property is preserved, all four singletons are false, and all three consecutive edge pairs are true. Of the 102 monotone read-once truth tables on four variables, exactly one satisfies these conditions, and it accepts the pair of endpoints. Since the endpoints belong to I, the original factor accepts I. This avoids any assumption about how many connected components are present. Run `python3 -B four_vertices.py` to replay the enumeration, which recursively splits the allowed four-variable set into disjoint child sets for AND and OR.

## Integer certificate

Enumerating maximal independent sets gives the following multiplicities and weights.

| Selected vertices in the maximal independent set | Number | Weight per set |
|---:|---:|---:|
| 6 | 52 | 1 |
| 7 | 468 | 1 |
| 8 | 156 | 1 |
| 10 | 26 | 0 |
| 13 | 2 | 5 |

The total weight is 686. A single canonical factor rejects at most 14 sets and at most 10 weight units. Both capacities are attained. To check the latter bound, for each maximal I the program enumerates all independent subsets T of its complement. Each gives exactly one S by taking the remaining vertices. The enumerator records all 4,363,558 matching pairs (I,S) and inspects all 2²⁶ choices of S. It also evaluates the maximizing examples by explicitly building connected components. Covering weight 686 with factors of capacity 10 takes at least 69 factors.

Run the C++20 checker with the following commands. Its table uses approximately 256 MiB.

```sh
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
c++ -O3 -std=c++20 check.cpp -o "$build_dir/check"
"$build_dir/check" | diff -u expected.txt -
```

## Unrestricted wire lower bound

Splitting the earliest shared wire gives a read-once factor cover of size at most 2ʰ, where h counts the distinct wires used twice or more within the cone. The 69-factor lower bound therefore forces seven shared wires. Counting their extra argument occurrences in the essential 26-input graph gives at least 32 gates including the virtual AND and **at least 31 stored gates**. The proof accounts for unary gates, repeated arguments and default false reads. [DAG argument and limitations](DAG.md) · [Exact fractional cover](../fractional/README.md)
