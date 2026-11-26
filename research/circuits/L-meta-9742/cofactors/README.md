# What an unrestricted cofactor recurrence proves

For the assigned monotone AND/OR circuit model, this recurrence alone yields **29 gates**. It visits all 67,108,864 vertex subsets, including 30,185,957 nonempty induced graphs with no isolated vertices. The separate graph theorem gives 38. The computation identifies the limit of this particular recurrence on the instance. [Output](expected.txt) · [Stronger graph theorem](../lower/README.md)

Write L(G) for the computed lower bound. Discard isolated vertices, set L to zero for an edgeless graph and to one for a single edge. With n remaining vertices the edge function depends on every vertex, giving a lower bound of n−1 binary gates by counting the inputs of the output cone.

For each vertex v compute two additional bounds. Pinning v false leaves G−v. Pinning v true leaves the OR of its d distinct neighbors as individual variables and the edge function of the induced graph H on the vertices outside v and its neighborhood. With an edge left in H, the bound on this last cofactor is d+L(H). Setting each singleton variable to false in succession eliminates at least one gate that reads it: the variable is essential at each stage and the function always contains the independent residual edge term. For an edgeless H the cofactor is simply the OR of d inputs, costing d−1. Denote the two bounds by b₀ and b₁.

In a minimum circuit for a graph with at least two edges, propagate constants, bypass copies, remove unused gates and discard any gates with duplicate inputs. All remaining gates have two inputs. Each active variable has a reader. Substituting either constant into any reader removes at least that gate, so 1+max(b₀,b₁) is a lower bound for each active variable.

The first binary gate receives two distinct variables. A pin of either operand to the absorbing value makes the first gate constant and simplifies at least one direct consumer as well. The gate has a consumer since the target depends on at least three variables. A neutral pin saves at least the first gate. The endpoint score for AND is max(2+b₀,1+b₁), and for OR it is max(1+b₀,2+b₁). For each operation take the second-smallest endpoint score, counting ties. This minimizes the larger score of two distinct endpoints. Take the smaller of the two operation bounds, then maximize it with the essential-variable and general-pin bounds. Subsets are processed in increasing bitmask order, so every residual bound is available when needed.

Run from this directory with a C++20 compiler and Python 3. The program also compares its lower bound on every isolate-free subset with a constructible star-circuit upper bound.

```sh
build=$(mktemp -d)
c++ -std=c++20 -O3 bound.cpp -o "$build/bound"
python3 -B extract.py | "$build/bound" | diff -u expected.txt -
```
