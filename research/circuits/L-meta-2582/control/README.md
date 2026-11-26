# Smallest two-input circuits separating scalar reads from joint read-2

Consider a two-input binary acyclic AND/OR circuit computing the single edge x AND y. Its sole prime implicant is the pair. In the upstream definition, the scalar test minimizes each endpoint's leaf count separately. The joint test asks for a single unfolded proof tree bounding both counts.

Four gates suffice for a circuit to pass the scalar read-2 test and fail the joint read-2 test. Take a = x AND y, b = x OR y, c = a AND b and d = a AND c. All four gates read distinct wires within the gate. The two possible output count pairs are (2,3) and (3,2). The scalar minima are both two. The joint minimum is three.

Five gates suffice to reduce both scalar minima to one while the joint minimum stays three. Compute xy, xx and yy with three AND gates, then compute (xx OR yy) AND xy. The output count pairs are (3,1) and (1,3). Repeated inputs in the xx and yy gates follow the root circuit model.

The upstream ReadK documentation describes the per-edge Pareto algorithm and gives the earlier k=1 separation (xy) AND (x OR y). On its only prime implicant, the scalar minima are one while the joint minimum is two. [Pinned definition and attribution](https://github.com/open-goat/pequalnp-proofs/blob/1972ec9f567e2b3c90b0adc5472172f7e5ddfab0/lean/PEqualNP/Defs/ReadK.lean#L39)

## Exhaustive minimality check

At each position enumerate both operations and all unordered pairs of earlier wires, allowing a repeated wire. AND and OR commute with respect to their Boolean values and exponent sets. Feed-forward labels distinguish wires even when two wires have identical contents. Each program takes the last gate as output. An earlier output could drop its unused suffix, and an input alone fails to compute x AND y. These observations include all possible smallest circuits in the two-input model.

A wire carries a set of exponent pairs capped at three in each coordinate. OR takes union. AND takes every pairwise sum and caps the result. Positive multiplicities never decrease under multiplication, and the cap preserves the thresholds 0, 1 and 2 exactly. With two inputs and exactly two operands per gate, each wire has a nonempty parse set. The circuit computes x AND y exactly when all its parses contain both variables. Among these circuits keep the ones with no parse in the square of side two (both coordinates at most two). Then compute the two scalar minima.

| Gates | Programs | Both scalar minima ≤2 and joint >2 | Both scalar minima ≤1 and joint >2 |
|---:|---:|---:|---:|
| 1 | 6 | 0 | 0 |
| 2 | 72 | 0 | 0 |
| 3 | 1,440 | 0 | 0 |
| 4 | 43,200 | 13 | 0 |
| 5 | 1,814,400 | 1,905 | 107 |

Thus four gates and five gates, respectively, are exact minima in this model. The counts enumerate programs with unordered operands and allow unused earlier wires. The minimum claims come from this Python exhaustion. Lean independently checks the two witnesses against the upstream definitions, including that both compute x AND y, the pair is the only prime implicant, and each circuit has global joint read exactly three.

For a nonempty simple bipartite graph the four-gate pattern gives a corresponding separation on every edge. Take A to be an OR of the distinct edge conjunctions and B an OR of all inputs. On a prime edge A has only the proof counts (1,1), and B permits either endpoint alone. Therefore A AND (A AND B) computes the same graph function and has precisely the two tradeoff counts on every prime. A already supplies a smaller read-1 representative. This graph observation is a mathematical argument.

## Reproduction

Run the Python checker from this directory and compare with the recorded census. In a pinned upstream Lean checkout at commit 1972ec9f567e2b3c90b0adc5472172f7e5ddfab0, build PEqualNP.Defs and run the Lean file through the project's lake environment.

```sh
python3 enumerate.py | diff - census.txt
# From the upstream lean/ directory
lake env lean /path/to/ScalarControl.lean
```
