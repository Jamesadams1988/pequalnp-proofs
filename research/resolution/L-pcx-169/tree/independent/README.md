# Independent literal-query tree calculation

For the unary pigeonhole formula with five pigeons and four holes, the minimum number of leaves in a binary variable-query tree is **189**. At a leaf, the partial assignment must falsify an original formula clause. Repeated uses of a leaf count separately.

Run from this directory with a C++17 compiler. The table takes about 126 MiB of memory.

```sh
c++ -O3 -std=c++17 row_tree.cpp -o ./php54-row-tree
./php54-row-tree
```

The expected counts are reproduced below.

```text
five ternary rows, four labelled columns
ranked multisets 32801517 nonterminal 1300448 terminal 31501069
inequivalent variable choices over nonterminal row multisets 10775792
all labelled query choices over those states 11650032
maximum optimal value 189 empty-state optimum 189
```

Each pigeon has 81 possible partially assigned rows, one ternary digit per hole. The program sorts the five rows, so states equivalent under a pigeon permutation share a table entry. Every hole retains its original label. A sorted tuple with entries `r[0] … r[4]` has multiset rank `Σ choose(r[k] + k, k + 1)`. All 32,801,517 ranks are visited once. The program checks the rank order during traversal.

A row with four false bits falsifies its pigeon clause. A column with two true bits falsifies a collision clause. Each such state has cost one. At all other states, the value is the minimum over unassigned bits of the sum of the two child values. Children of identical rows give equal values for the same hole. Setting an unknown ternary digit to either truth value strictly increases the multiset rank. Descending rank order therefore supplies both child values for every query.

This calculation concerns tree leaves. Ordinary resolution can share a line among several later inferences, so the result leaves the unrestricted proof-length question open.
