# Exact ordinary tree size for unary PHP(5,4)

The smallest Boolean decision tree that always identifies a falsified input clause has **189 leaves**. A pure ordinary resolution refutation tree has the same minimum, or **377 line occurrences** counting leaves and joins. If original axioms can each be stored once but every derived line is used once, the minimum becomes **233 lines**. The shared resolution DAGs allowed by the desk can be smaller.

The inputs are 20 independent Booleans. A row of four zeros falsifies a pigeon's existence clause. Two ones in a column falsify a collision clause. A pigeon may have more than one true entry in its row. An optimal nonterminal tree chooses a variable and adds the optimal leaf counts of its two children. Every assignment with an already falsified clause costs one. This recurrence is exact by induction on the remaining unknown variables. The calculation allows all fresh variable choices at every node.

The column-based implementation stores 112 possible live columns. It omits columns with two true entries because they immediately terminate. Sorting four columns preserves the labeled problem up to hole renaming, leaving 6,913,340 multisets. Assigning a fresh variable strictly increases its column ID and hence the multiset rank, so reverse rank computes all child costs before their parents. The independent implementation instead sorts pigeons and keeps holes labeled. It checks 32,801,517 row multisets and also obtains 189. [Column implementation](tree_table.hpp) · [Independent row computation](independent/README.md)

Lean proves the correspondence in both directions for pure resolution. The numerical optimum comes from the exhaustive integer calculations. The accompanying 377-line trace is an explicit upper bound, with each of the 376 nonroot lines used exactly once. It has 65 existence-axiom and 124 collision-axiom leaf occurrences, and 188 resolutions. Deduplicating the 45 original axioms alone saves 144 lines. [Formal correspondence and trace audit](formal/README.md) · [Lean witness](witness/README.md)

From this directory, compile with a C++20 compiler. The optional sampler generates the canonical tree, then searches optimal trees under fixed variable preferences for identical clauses to share. With 10,000 orders from the supplied seed its shortest DAG used 185 lines. That search therefore did not improve the public 157-line construction. The shuffle sequence can vary across C++ standard libraries.

```sh
c++ -O3 -std=c++20 tree.cpp -o tree && ./tree
c++ -O3 -std=c++20 sample_trees.cpp -o sample_trees
./sample_trees 10000 reproduced-tree.json best-dag.json
python3 -B formal/verify_tree.py reproduced-tree.json --expect-377-tree
```

A separate exact calculation permits one chosen Hall clause to be shared between two trees. Depending on the number of holes in the clause, the optimum is 223 or 233 lines. [Two-phase calculation and certificates](one-hall/README.md)
