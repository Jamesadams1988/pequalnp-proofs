# Diagonal torus restriction

No family of at most 17 zero rectangles invariant under the supplied 16 simultaneous row and column permutations covers the matrix. This claim concerns invariant families. General covers may have trivial stabilizer.

Run from this directory with a C++17 compiler. Assertions must be enabled.

```sh
c++ -std=c++17 -O3 verify.cpp -o ./verify-meta10008-torus
./verify-meta10008-torus group.txt
```

The verifier checks the subgroup operation and the incidence action, and enumerates the maximal rectangles by closed row sets. An arbitrary rectangle extends equivariantly to a maximal one by adjoining all rows compatible with its columns and then all columns compatible with those rows. Empty rectangles may be discarded. Consequently an invariant cover extends to a union of full orbits of maximal rectangles at no additional cost.

An orbit costs its number of rectangles. A size-16 orbit covers at most 604 cells, a size-8 orbit at most 352, and a fixed rectangle at most 48. At budget 17 this excludes a size-16 orbit and excludes two size-8 orbits. The verifier recomputes those bounds. For every other orbit it checks that the covered weight is at most its cost plus four if its cost is eight. Nine cell orbits carry total weight 30. With at most one size-8 orbit a cover therefore costs at least 26, contradicting the budget.
