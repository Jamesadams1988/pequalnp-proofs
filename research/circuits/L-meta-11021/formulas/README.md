# Partial edge tests and reusable conjunctions for L-meta-11021

For every subset R of the twelve assigned edges, the minimum monotone formula accepting the edge assignments in R and rejecting every independent set is exactly **|R| + τ(R) leaves**, where τ(R) is the vertex cover number of the subgraph with edge set R. A formula may accept the remaining edges. Use the empty expression for R empty. The finite exhaustive lower bound allows arbitrary nesting of binary AND and OR gates. A star partition attains every one of the 4096 minima.

## Consequence for sharing

Allow arbitrary preprocessing by AND gates on the raw variables and prior AND wires, followed by an arbitrary binary AND/OR formula. The formula can use any raw variable and reuse any preprocessing wire any number of times. Require the preprocessing to include the indexed raw pair product for each edge in a fixed subset S. All gates count, including unused ones. The exact minimum for the assigned function is

**11 + |S| + τ(E ∖ S) gates.**

For S empty this is 16. Exactly two nonempty compulsory sets also attain 16, the individual edges (0,4) and (1,5). Over all S the frequency distribution is

| Total gates | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Sets S | 3 | 45 | 255 | 729 | 1208 | 1147 | 584 | 125 |

Every nonconstant preprocessing wire is the conjunction of a subset of the raw variables. Unary copies can be replaced with raw wires. A conjunction of three or more distinct variables, or of two nonadjacent variables, is false on every minimal true input. Replacing its formula occurrences by false preserves acceptance of each minimal true input and cannot create any new acceptance on negative inputs. Simplify constants. The only remaining useful preprocessing signals are edge indicators, each active on just one minimal true input.

Let B be the set of distinct edge indicators that actually occur in the suffix. Replace every such occurrence by false and simplify the formula to a residual formula with L₀ leaves. It still accepts every edge of E ∖ B and rejects every independent set. If the suffix originally had L leaves, then L ≥ |B| + L₀ because each distinct indicator consumed at least one of the original leaf occurrences. This remains true for an identically false residual, assigned zero leaves. Hence L ≥ |B| + |E ∖ B| + τ(E ∖ B) = 12 + τ(E ∖ B). There are at least |S ∪ B| paid preprocessing gates. Since adding one edge can increase minimum vertex-cover size by at most one, τ(E ∖ S) ≤ τ(E ∖ B) + |B ∖ S|. Counting the L − 1 suffix gates gives the claimed lower bound. For the upper bound, OR the |S| compulsory indicators with a minimum star formula for E ∖ S. Their total leaf count in the suffix is |S| + |E ∖ S| + τ(E ∖ S). This proves exactness, including optional additional preprocessing gates.

## Finite proof of the residual minima

The positive tests are the twelve two-endpoint assignments. The thirteen negative tests are all maximal independent sets, found by examining the 512 assignments. Every independent set is contained in one of these negative tests, so a monotone formula which rejects them rejects every independent set.

Relative to the *full* target on these 25 tests, record the error set of each formula. On positive tests, AND takes the union of its children's errors and OR their intersection. On negative tests the two operations exchange roles. Both are inclusion-preserving. A child may be replaced by any formula of equal or smaller leaf count whose error set is contained in its own. Thus the recurrence over positive splits of the leaf count, discarding dominated error masks, retains enough information to find the smallest formula accepting every required subcollection and rejecting all negative tests. A retained zero-negative-error formula with true edge set C gives an upper bound on the residual cost of every R contained in C. Whenever a formula discarded as dominated could give such an upper bound, its dominator is also safe, covers a superset of its edges, and has no greater leaf count. Seventeen leaves suffice to reach the entire edge set, thereby bounding all residuals.

Independently, a minimum vertex cover of R assigns each edge to one of its endpoints in the cover. For each center, AND it with the OR of the leaves assigned to it and OR the resulting stars. This gives a formula with |R| + τ(R) leaves. The replay enumerates all 512 vertex subsets to compute τ for each R and compares against the independently obtained formula optimum for every R.

Compile and run with a C++20 compiler and Python 3.

```sh
c++ -O3 -std=c++20 residual.cpp -o residual
python3 verify.py ./residual
```
