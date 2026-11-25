# Signed live-wire enumeration for L-meta-12096

The target is the 64-bit table `0xfe80fe00fe00e800`, with input 0 least significant. `signed.cpp` searches acyclic two-input AND/OR networks with free complemented wires. Each generated wire has a complete 64-row table. The unrestricted count below is a binary-gate count. The project also charges for each physical NOT gate.

## Reproduce

From this directory, run the following commands.

```sh
g++ -std=c++20 -O3 -o signed signed.cpp
python3 replay_controls.py
./signed 10 0
./signed 11 0
./signed 12 1
```

A result of `fits=0` excludes every circuit at or below the requested budget. The additional mode `./signed 11 1` uses only AND and OR. The source caps budgets at 12. Its input contract explicitly requires six essential variables and value zero on the all-zero assignment. The target meets both requirements. The control script includes a genuinely signed positive control and the earlier kernel-checked eight-gate table for L-meta-15250.

## From project circuits to a signed network

Each input and each generated wire represents its signal together with its free complement. Normalize that pair to the truth table taking value zero at the all-zero row. A physical NOT then costs no binary gates. A binary AND or OR of two literals, normalized at row zero, is precisely one of `a & b`, `a | b`, `a & ~b`, and `~a & b`. This follows by enumerating the two independent input signs and applying De Morgan to the output sign. The test for an accepting output compares the entire table against the target.

The original model sends out-of-range, forward, and self-references to false at the moment they are read. The empty AND and OR gates are constants. A unary AND or OR copies its input. NOT reads its first input (or false when none exists) and ignores a second input. These cases introduce only constants, literals, or aliases in the signed network. Repeated operands similarly give constants or literals. Constant propagation, bypassing aliases and complement-equivalent wires, and removing gates with no path to the output preserves a nonconstant output without increasing the number of binary gates. All six variables are essential, so the output cannot be a constant, an input, or its complement. Hence zero gates and all output-wire anomalies have been accounted for.

## Why the finite traversal is complete

Fix a minimum signed network with globally distinct, nonconstant normalized wire functions. Choose a topological order and initially keep its six inputs, all of which are used. Immediately before every binary gate, the intended live set contains every earlier wire with a remaining use. The gate consumes two distinct live wires. Its result becomes live. Exactly those consumed wires with later uses must also remain live. The four choices of `keep` exhaust those possibilities. Distinct gates may read the same live wire, so the traversal covers shared subcircuits. Keeping only the needed wires gives one represented traversal for every minimum circuit.

A bank of `m` live wires requires at least `m-1` further gates to reach a single output, since one binary gate can reduce the live count by at most one. The width check uses that bound after inserting each candidate gate. Any exact target hit returns at once, including before the last permitted gate. All smaller positive gate counts are therefore covered by a single run. No padding hypothesis is used.

If two assignments with opposite target values agree on every live wire, they agree on every subsequent signed computation. For monotone gates, a target-positive assignment must have some live wire that is true there and false at the target-negative assignment. The inexpensive per-candidate test uses 123 pairs from the minimal-positive/maximal-negative pairs and all hypercube edges that change the output. On entering a state, the updated implementation applies the corresponding criterion to all 26 × 38 positive/negative row pairs. These tests are necessary conditions only. The gate-output test uses all 64 rows.

States are sorted lists of exact wire IDs with their remaining budget. The work cache uses full state equality. A collision may evict an older state and repeat work. At the first move, the search may identify banks under permutations of inputs 0, 1, 2 and of inputs 4, 5. Each candidate permutation is checked on all 64 target bits before use. A bank is pruned only after an equivalent bank was reached. An interned image that is absent only reduces the reuse of earlier work.

A second implementation of the signed operation encoding tested all 60 first moves without symmetry pruning at budget ten. It agreed with the optimized search on the exclusion of every circuit within that budget. The eleven-gate run with symmetry checked the same target on all 64 inputs and found no circuit.

With eleven binary gates and free complementation, the search returned `fits=0` after interning 608,259 distinct wire tables. With twelve monotone gates it returned `fits=0` after interning 45,853 wire tables. On the test machine these checks took about 74 and 39 seconds.
