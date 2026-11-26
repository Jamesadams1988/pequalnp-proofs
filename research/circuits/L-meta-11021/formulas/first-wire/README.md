# Reusing one prescribed first gate

For each paid first gate, let a binary AND/OR formula use its output and all raw variables as often as it wishes. The exact minimum is 16 or 17 gates. Two of the 36 ANDs and 21 of the 36 ORs attain 16, while all nine NOTs require 17. The two ANDs are (0,4) and (1,5). The raw formula optimum is 16 gates. A prescribed constant or copy gate costs one additional gate.

The recurrence from L-meta-11031, instantiated on the present edges, enumerates nondominated error masks of formulas of each leaf count over the twelve edges and thirteen maximal false assignments. It admits the paid first gate's truth value as a reusable leaf. Error-set inclusion remains a valid dominance relation even for a negative feature since the continuation operations are positive. Boundary exclusion gives a lower bound on circuits correct everywhere. For all 17-gate cases an unused first gate and a 16-gate star formula suffice. Of the 23 first gates attaining 16, all but one occur in a partition of the edges into five stars. For s = x₆ ∨ x₈, the remaining case, take the disjunction of the following terms.

- x₁ ∧ x₅
- x₇ ∧ (x₄ ∨ x₂)
- x₀ ∧ (x₄ ∨ x₇ ∨ x₅)
- s ∧ (x₃ ∨ ((x₂ ∨ x₈) ∧ (x₁ ∨ x₄ ∨ x₆)))

The verifier checks this formula on all 512 assignments and independently enumerates the first wires possible in star partitions. It also checks why unrestricted internal negations need different tests. An eleven-gate signed formula passes all 25 extremal tests and the two constant assignments while disagreeing on 109 other inputs.

```sh
c++ -O3 -std=c++20 first.cpp -o first
python3 verify.py ./first
```

The fourth field of first-results.txt counts leaves in the continuation. This equals the total number of gates with a paid prefix and exceeds the gate count by one for the raw baseline.
