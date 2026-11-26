# Formula size and the effect of reusing the first gate

The edge function of L-meta-11031 has exact binary AND/OR formula size **16 gates**, or 17 leaves. If the first gate computes a fixed function of raw inputs and its output can be reused freely in an AND/OR formula, the optimum over all first gates is still 16.

| First-gate function | Cases | Minimum 16 total gates | Minimum 17 total gates |
|---|---:|---:|---:|
| NOT of a raw input | 9 | 0 | 9 |
| AND of distinct raw inputs | 36 | 3 | 33 |
| OR of distinct raw inputs | 36 | 23 | 13 |

These are the 81 nontrivial first functions. If the circuit model also permits aliases and constant wires as first gates, such a gate costs one and provides no savings in the continuation. The computation counts every listed gate, including an unused first gate. The continuation may take negated information from a first NOT. Its internal nodes are binary AND and OR. The other gates have formula fanout. Arbitrary later sharing and internal negations are outside this calculation.

## Lower bounds

There are 12 minimal true assignments, one per edge, and 11 maximal false assignments. Among all 512 input assignments exactly 60 are false. For every formula size, enumerate achievable sets of errors on the 23 designated tests. If a candidate at the same or lower cost has a subset of the errors, retain that better candidate. On a positive test, AND takes the union of its children's errors and OR takes the intersection. On a negative test the roles are reversed. Both combinations preserve inclusion, so dominance pruning cannot remove the only successful expression.

The one-leaf expressions are the raw inputs and, in a forced-first-gate case, its output. The recurrence tries each positive split of the leaf count and both ways to combine the child formulas. Its first zero error set gives the exact boundary optimum. Any circuit correct on the full cube must agree on these tests, including when the extra input feature is negative. Without a first gate, an L-leaf continuation costs L−1 binary gates. With a paid first gate it costs L gates in total.

## Upper bounds and controls

The three ANDs attaining 16 gates are x₀ AND x₄, x₁ AND x₅, and x₂ AND x₆. Among the 26 first-gate functions attaining 16, 25 occur in a partition of the edges into five stars. Within each star an OR combines its leaves, then an AND tests its center; four further ORs combine the stars. The verification script enumerates every way of assigning the twelve edges to endpoints. For the remaining first gate, s = x₇ OR x₈, take the OR of the following four terms:

- x₂ AND x₆
- x₁ AND (x₅ OR x₆)
- x₀ AND (x₄ OR x₆)
- s AND [x₃ OR ((x₂ OR x₅ OR x₇) AND (x₀ OR x₄ OR x₈))]

The formula uses s exactly once and agrees on all 512 assignments. Thus all 26 improvements over a disconnected first gate have witnesses even without reusing s. For every other first function, prepend the prescribed gate to a 16-gate star formula and leave its output unused. This attains 17 total gates and supplies a full-cube upper bound for the nine NOT cases independently of boundary sufficiency.

## Replay

Compile the C++20 decision program and run the checks below. The replay validates the upper-bound cases independently and compares all 82 searches, including the raw baseline, with the recorded leaf counts.

```sh
c++ -O3 -std=c++20 first.cpp -o first
python3 verify.py ./first
```

The retained error-set recurrence adapts the earlier L-meta-17336 formula computation to the new graph and all possible first gates.
