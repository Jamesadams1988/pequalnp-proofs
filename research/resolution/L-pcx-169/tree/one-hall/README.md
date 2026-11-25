# Exact cost of reusing one Hall clause

In an ordinary refutation of unary PHP(5,4), allow free reuse of the 45 original axioms. Choose a set T of k holes and a set P of k+1 pigeons. First derive the positive Hall clause H stating that at least one pigeon in P occupies some hole outside T. This one derived occurrence can be used arbitrarily often. Each other derived occurrence can be used at most once. Hole and pigeon permutations preserve the rules, so the identities of P and T do not affect the result.

| Holes in T | Minimum leaf count under H=false | Minimum leaf count with H available | Exact total lines |
| ---: | ---: | ---: | ---: |
| 1 | 3 | 177 | **223** |
| 2 | 11 | 169 | **223** |
| 3 | 43 | 147 | **233** |

**Lower bound.** To falsify H, initially set all variables in P × (holes outside T) to false. Traversing any preparation tree from that restriction gives a tree that finds a falsified original axiom. The first numeric column is the unrestricted tree table at that state. For the rest of the proof add H to the original axioms as a possible leaf. When every variable of H is false this costs one leaf. Otherwise minimize over all binary queries as in the original calculation. Column permutations within T and its complement preserve both the original axioms and H. The two-phase table therefore sorts the columns within those two groups. The three tables contain 26,931,968, 40,043,584 and 26,931,968 states. [Recurrence](hall_table.hpp) · [Tree correspondence](../formal/README.md)

A binary proof tree with L leaves needs L−1 resolutions. Summing the two resolution counts and adding 45 gives each bound in the last column. All 45 distinct axioms are indispensable. To witness this for an existence axiom, leave its pigeon absent and put the other four in distinct holes. To witness it for a collision axiom, put its named pair in its named hole, and put the other three pigeons in the other three holes bijectively. These assignments satisfy all remaining axioms.

**Attainment.** The extractor returns the exact positive clause H in the first phase and the empty clause in the second. The traces reach the three stated bounds. The independent checker verifies each signed resolution, the unique occurrence and reuse count of H, and that every other derived occurrence has one reader. Without any reusable derived clause, 45 original axioms plus 188 resolutions give a minimum of 233 lines when axiom occurrences alone are shared. The desk allows every derived line to be reused. [Tracing algorithm](hall_witness.cpp) · [Certificate checker](verify.py)

Run the following in this directory with a C++20 compiler and Python 3.10 or newer. The largest table takes roughly 180 MB of working memory.

```sh
python3 -B verify.py
c++ -O3 -std=c++20 one_hall.cpp -o one_hall && ./one_hall
c++ -O3 -std=c++20 hall_witness.cpp -o hall_witness && ./hall_witness regenerated
for k in 1 2 3; do cmp "regenerated$k.json" "hall$k.json"; done
```
