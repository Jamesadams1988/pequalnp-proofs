# Read-once trees for six pigeons in one hole

The six variables describe one hole. Its 15 premises are the pair inequalities `x_i+x_j ≤ 1`. The capacity target is `sum(x) ≤ 1`. For the final-hole problem add the premise `sum(x) ≥ 2` and target `0 ≤ -1`.

The search allows binary addition and arbitrary positive integer divisors dividing every variable coefficient. It rounds the right side down in the `≤` orientation. Each premise appears at most once and each derived line has at most one use. Scalar multiplications and Boolean source inequalities are outside this search.

Every feasible proof in this class must use all the designated sources. Omitting an edge lets its two endpoints be one and the other variables zero. Omitting the total in the final-hole problem admits the all-zero assignment.

For each subset of edges, the verifier builds the full catalogs of lines derivable with exactly those leaves. The pure catalog has only the chosen edges. The mixed catalog includes the total exactly once. At the last addition the children partition the leaves, and in a mixed addition exactly one child contains the total. After these sums the verifier inserts every legal division result. A chain of divisions by positive integers gives the same result as one division by their product. When the coefficient vector is zero, divisors greater than the absolute RHS all give the same floor. These observations establish completeness by induction on the edge mask.

Both catalogs have exact integer encodings. A pure coefficient never exceeds its original degree, at most five, and its RHS never exceeds 15. A mixed variable coefficient stays at least −1 and its RHS at least −2, since it combines one total with nonnegative edge lines and any cuts. The encoded sums therefore cannot carry between bytes.

Run with a C++17 compiler supporting the trailing-zero builtin.

```sh
c++ -std=c++17 -O3 readonce.cpp -o ./meta-9708-readonce
./meta-9708-readonce
```

The attainable full-mask constant bounds are listed in `results.txt`. A general cutting-planes derivation can use scalings, sharing, Boolean axioms, or lines spanning multiple holes.

## Standard single-hole capacity

The usual unrestricted construction has 36 lines. Start with all three edges of a triangle, add them using two sums, and divide by two. For each new vertex, let the old clique have size `m` and capacity `A ≤ 1`. Scale its capacity by `m−1` and add the `m` new edge axioms. The result is `m(A+x_new) ≤ 2m−1`. Divide by `m`. The triangle costs six lines. The later stages cost eight, ten and twelve, respectively.

The package includes an independent executable trace in [traces.py](../traces.py). It checks the 36-line capacity and combines five such capacities with the six pigeon clauses into a 196-line refutation.
