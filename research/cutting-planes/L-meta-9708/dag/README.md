# Exact cost of a normalized one-hole clique DAG for six pigeons

The minimum is 36 CP lines. This calculation allows a derived clique inequality to be reused in arbitrarily many later cuts.

## Model

Write C(T) for the line saying that the sum of the indicators indexed by T is at most one, and start from the 15 pair inequalities. A cut with output C(T) combines pair axioms and completed proper-subclique inequalities using binary addition and arbitrary positive integer scaling. It ends with a single division that gives C(T). A scalar multiplication costs one instruction regardless of its multiplier. Addition and scalar-multiplication lines can be shared within a cut. Raw intermediate sums and scaled multiples shared **across** cuts are outside this model. Boolean axioms, pigeon inequalities, intermediate lines with other right-hand sides retained across cuts and unrestricted CP proofs are also outside this calculation.

Every pair axiom is necessary. If the axiom for pair {a,b} is omitted, the integer assignment setting those two coordinates to one and all other coordinates to zero satisfies every available pair axiom and violates the conclusion. Thus a 35-line proof has at most 20 nonaxiom instructions. Repeated completed clique labels can be eliminated by redirecting their uses to the first occurrence. The output supports of nonredundant cuts have size three through six and can be ordered by increasing cardinality because every input is a proper subclique.

## Bound for one cut

Let the distinct child cliques have positive integer weights w(B) after expanding the additions and multiplications. For a divisor d, the coefficient of every vertex in T is exactly d and the total weight W satisfies d ≤ W < 2d. For every nonempty Q contained in T, summing vertex coefficients gives d|Q| = Σ w(B)|B∩Q|. If every B hit at most half of Q, the right-hand side would be at most W|Q|/2 < d|Q|. Consequently some B hits more than half of Q.

For a two-element Q, a child must contain the pair. If no selected nonedge child contains it, its pair axiom is mandatory. For Q of size four or six, a nonedge child must contain more than half of Q. These necessary conditions are used even when optional additional pair axioms are present. At least three distinct children are necessary. If there were just two proper children, a vertex missing from each forces the other child's weight to be at least d, contradicting W < 2d. A vertex missing from both is impossible outright. Hence each cut costs at least three instructions and at most six cuts fit a nonaxiom budget of 20.

Fix the complete set of nonedge children of a cut. Count every one of these children and every mandatory pair to obtain t. Combining t distinct sources requires at least t−1 binary additions, to which the division adds one line. Equality requires exactly these sources, each appearing with coefficient one, with no multiplication. To see this, delete unused computation and count undirected edges in the local connected addition circuit. With t sources and t−1 binary gates, the 2(t−1) incoming edges of the gates already equal the number of vertices minus one. Any repeated input or sharing would introduce a cycle in the undirected multigraph. Thus the circuit is a tree in the equality case. If the unit-weight family does not have constant incidence d and t < 2d, charge **one** additional instruction. This charges at most one extra even if many scales or other pair inputs are needed. These per-cut bounds can be added because all work except completed clique labels is local to its cut.

## Enumeration and witness

The program enumerates subsets of up to five of the 41 proper nonedge clique labels (20 triples, 15 quadruples and six quintuples) in nondecreasing size. The final cut is always the full six-vertex clique. For each target it tries every subset of its available proper nonedge children. It keeps a prefix only if each included cut passed the necessary majority tests with some choice of children. Larger labels could never repair a prefix that failed. The program minimizes the operand-only and local-instruction bounds separately. The values in the table are exact minima **of these lower bounds**. Only the overall minimum proof cost is claimed exact.

| Derived labels including final | Surviving prefixes | Operand-only bound | Local-instruction bound |
| ---: | ---: | ---: | ---: |
| 1 | 1 | infeasible | infeasible |
| 2 | 20 | infeasible | infeasible |
| 3 | 250 | infeasible | infeasible |
| 4 | 2,370 | 18 | 21 |
| 5 | 18,485 | 20 | 22 |
| 6 | 122,699 | 22 | 24 |

An explicit 36-line construction starts from an edge and extends from r−1 to r vertices for r=3,4,5,6. Multiply the old clique by r−2, add the r−1 pair axioms incident to the new vertex and divide by r−1. The sum has coefficient r−1 at every vertex and right-hand side 2r−3. The first multiplier equals one and requires no instruction. The cuts use 3, 5, 6 and 7 instructions respectively, totaling 21 in addition to the 15 axioms.

Reproduce in this directory with the following commands.

```sh
c++ -O2 -std=c++17 -Wall -Wextra -pedantic clique_dag.cpp -o ./clique_dag_k6
./clique_dag_k6 | diff - bounds.txt
```
