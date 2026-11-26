# Testing joint read-2 on three finite projective planes

The packed checker stores a set of exponent pairs (a,b) in a nine-bit integer. Bit 3a+b means that one proof tree reads the selected point a times and the selected line b times, with both counts between zero and two. Other input wires start empty. OR is bitwise union. For AND, each set bit of the first input shifts the second input after masking away coordinates that would exceed two. This mask also prevents a shift from wrapping into the next row. A discarded exponent cannot decrease at a later AND.

The baseline uses a separate implementation and representation. It stores Python sets of pairs with coordinates in {0,1,2,3}, unions them at OR gates and enumerates all pairs of elements at AND gates, adding componentwise and capping each sum at three. Projection drops points with a coordinate of three. These are the rules of the upstream joint vector specification for two distinct inputs. The baseline is a Python replay of those rules. Lean has its own executable definitions. The test compares the baseline's projection against the packed word at **every gate for every pair**, including nonincident point–line pairs. A separate exhaustive arithmetic test checks all 262,144 ordered pairs of nine-bit words against direct bounded set addition. [Upstream joint-count definition](https://github.com/open-goat/pequalnp-proofs/blob/1972ec9f567e2b3c90b0adc5472172f7e5ddfab0/lean/PEqualNP/Defs/ReadK.lean)

For q=2,3,4, the points and dual lines are the vectors in the corresponding three-dimensional coordinate space whose first nonzero coordinate is one. Incidence means zero dot product. Order four uses the binary field extension with t²=t+1. The program checks the size and degrees, as well as unique intersection on both sides. There are N=q²+q+1 points and N lines.

The point-star circuit A computes, for each point, its input AND the OR of its q+1 incident line inputs. It ORs all N results, using N(q+2)−1 gates. On an incident pair every successful parse has counts (1,1). The inflated circuit computes A AND (A AND B), where B is the OR of all 2N inputs. It adds 2N+1 gates. Its successful parses on an incident pair have exactly the counts (2,3) and (3,2). Hence each scalar minimum is two and no joint read-2 witness exists. The pair-specific scalar result is computed from the independent baseline. Nonincident pairs admit no successful parse in either circuit. Every emitted gate is binary AND or OR and reads two earlier wires. In the ordinary AO2 cost model fanout is free. The inflation keeps A's output available for both uses.

| q | Point–line pairs | Incident | Gates in A | Gates after inflation | Joint passes in A | Joint passes after inflation | Scalar passes after inflation | Gate comparisons |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 49 | 21 | 27 | 42 | 21 | 0 | 21 | 2,058 |
| 3 | 169 | 52 | 64 | 91 | 52 | 0 | 52 | 15,379 |
| 4 | 441 | 105 | 125 | 168 | 105 | 0 | 105 | 74,088 |

For the Fano plane both circuits matched the defining incidence condition on every one of the 16,384 input assignments, including 15,926 true and 458 false. The circuit evaluator uses one Boolean bit per assignment. A separate loop computes the graph predicate directly from each assignment. For orders three and four the all-input functional identity follows from the construction and Boolean absorption.

With the cap fixed, each packed gate takes constant work (at most nine mask-and-shift contributions). For m tested edges and g gates the checker takes O(m(N+g)) operations including input initialization and O(g+N) per-edge wire storage, apart from the optional operation memoization. This replay tests all N² pairs, so its pass visits N²g gates. The complete nine-bit operation table has constant size 512².

Run the following command with Python 3.10 or later from this directory.

```sh
python3 packed.py | diff - results.txt
```
