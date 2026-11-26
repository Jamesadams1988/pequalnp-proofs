# Two reusable gates for L-meta-17336

The graph has nine vertices and edges 04, 05, 15, 06, 26, 36, 17, 27, 47, 18, 38, 58. Its Boolean function is one exactly when the selected vertices contain an edge.

Fix the first gate to one of the seven values in the table. The second gate may apply NOT to any of the ten available wires or AND or OR to any two distinct available wires. The two gate outputs and all original inputs may occur arbitrarily often as leaves of an AND/OR formula for the final output. Each other internal gate has one use. This covers 100 second gates for each first gate.

For every such circuit, the total size is at least 17 when the first gate is NOT or AND, and at least 16 when the first gate is OR. The unrestricted size-15 question, which permits further sharing and later NOT gates, remains open in this calculation.

| First gate | Minimum leaves with first gate alone | Second gates with 15 suffix leaves | With 16 | With 17 | Total gate lower bound with both prefix gates |
|---|---:|---:|---:|---:|---:|
| NOT 5 | 17 | 0 | 21 | 79 | 17 |
| AND 5 6 | 17 | 0 | 21 | 79 | 17 |
| AND 5 7 | 17 | 0 | 21 | 79 | 17 |
| AND 5 8 | 17 | 0 | 29 | 71 | 17 |
| OR 5 6 | 16 | 14 | 86 | 0 | 16 |
| OR 5 7 | 16 | 12 | 88 | 0 | 16 |
| OR 5 8 | 16 | 15 | 85 | 0 | 16 |

The leaf counts measure exact separation on the boundary samples. For a full circuit they always give lower bounds. When all leaf signals are monotone they also give exact formula sizes for the full truth table. Every assignment with target value one contains a minimal positive assignment, and every assignment with target value zero lies under a maximal negative assignment.

## Recurrence

The positive sample consists of the 12 two-vertex edge assignments. Exhaustive enumeration of the 512 possible assignments gives 13 maximal independent sets for the negative sample. For nonempty subsets A and B of these samples, let D(A,B) be the fewest leaves needed to give one on all of A and zero on all of B.

* A single available signal is a solution if it takes these values on the entire rectangle.
* An OR root partitions A into two nonempty parts. Both children reject all B. Its cost is the sum of their leaf counts.
* An AND root partitions B into two nonempty parts. Both children accept all A. Its cost is the sum of their leaf counts.

Take the minimum of these alternatives, ranging over every proper bipartition. If one child already separates all samples, omitting the root gives a smaller formula. Otherwise each child handles at least one sample its sibling fails, and overlaps can be allocated to either child to obtain a disjoint split. Conversely the two optimal formulas for any split can be joined by the corresponding root. Induction on the number of samples proves the recurrence. Any two-input formula with L leaves has L−1 binary internal gates, giving total cost L+1 after paying for both prefix gates.

The implementation stores all nonempty table entries and processes positive subsets by cardinality. Within each cardinality it first tries positive splits, then negative splits in ascending mask order. Its initial sentinel 60 exceeds the 24-leaf formula that ORs the 12 edges. Every subproblem has a separator of at most 24 leaves. Two signatures that separate the same singleton pairs yield identical tables. If an existing signal separates all pairs separated by the added signal, that signal cannot improve the optimum. Constant and repeated-argument second gates likewise give at best the first-only boundary value.

## Replay

Run `python3 check.py --jobs 3` in this directory. This requires a C++20 compiler and Python 3. The driver compiles in a temporary directory and compares every computed entry with `expected.txt`. Each line after a first-gate heading records the second operation, left wire, right wire and minimum boundary-separating suffix leaf count. Operations 0, 1 and 2 denote NOT, AND and OR. The first gate is wire 9. The unary rows repeat their operand.

A second implementation enumerates the boundary assignments directly and computes rectangle splits in the opposite order. It can independently check all 707 entries or report the first discrepancy. [Independent verifier and replay instructions](independent/README.md)
