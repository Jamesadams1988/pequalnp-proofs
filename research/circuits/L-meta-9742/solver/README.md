# Exact SAT encoding for L-meta-9742

A monotone fan-in-two circuit of size at most 62 computes the listed graph's edge function **if and only if at least one of 17 representative CNFs is satisfiable**. They comprise all 14 OR cases (odd IDs from 1 to 27) and the three edge AND cases (IDs 8, 14, and 24). Each case has 151,032 Boolean variables and 8,246,306 clauses. All 28 original labeled cases remain available by ID for diagnostic use. The case tables appear in `stats62.json`. The 62-gate instances have no SAT or UNSAT result from this work.

## Generate a case

From the package root, list statistics or write one case to a new file with Python 3.

```sh
python3 solver/exact_synthesis.py --required-only
python3 solver/exact_synthesis.py --case 13 --dimacs L-meta-9742-case13.cnf
```

The generator streams DIMACS clauses to disk, reads the public assignment, and checks the packaged orbit partition against the reconstructed group. The default layout places `assignment.json` at the package root and the orbit table and group verifier under `symmetry/`. To change input paths, pass `--assignment PATH --orbits PATH`. The generator uses the Python standard library.

## Boundary assignments

The edge function is monotone. Its minimal true assignments are precisely the 51 two-vertex edges. Its maximal false assignments are the 686 maximal independent sets. Every true assignment contains a minimal true one and every false assignment lies in a maximal false one. Thus agreement of two monotone functions on these 737 tests suffices when one of them is the target.

For each subset A of the 13 left vertices, take B to be all right vertices with no neighbor in A. A union B is maximal independent exactly when A already contains every left vertex having no neighbor in B. Iterating all 8,192 left subsets gives each maximal independent set exactly once because its left part determines its right part. The verification script independently enumerates the same boundary after exchanging parts.

## Circuit and clauses

Each gate selects AND or OR and chooses one source for each of its two input ports. A gate may use any primary variable or any earlier gate. A separate selector for each port and source is shared across all test assignments. One positive clause requires at least one source, and sequential prefix clauses forbid selecting two sources. For any single selected source the prefix variables can be set to “a source through this position was selected,” which satisfies those clauses.

For each test, each gate has two input truth variables and one output truth variable. If a port selects a primary input, an implication sets its truth variable to the corresponding bit of the test. If it selects an earlier gate, two implications equate the port to that gate's output. Three clauses conditioned on AND enforce the AND truth table, and three conditioned on OR enforce the OR truth table. The last gate must equal the expected answer on each test. Three unit clauses fix the first operation and its ordered pair of input ports.

Given a satisfying assignment, reading the selectors yields a straight-line circuit. By induction on gate order the truth variables give its actual evaluation on each test, so the boundary argument proves correctness on all inputs. Conversely, any circuit with the specified selectors admits the evaluation and prefix assignments just described. Label renaming by a graph automorphism puts the first essential gate in one of the 28 cases, as proved in `symmetry/README.md`.

To relate these gates to the at-most bound, discard unused gates, propagate constants (including missing wires evaluated as false), and bypass unary gates and duplicate inputs. An empty AND or OR evaluates to a constant. The graph function depends on more than one variable, so this leaves at least one binary gate, and its first inputs are distinct variables. The surviving output can be placed last. Any shorter circuit can be padded to exactly 62 gates by repeatedly taking the OR of its output with itself. Later selectors allow repeated sources, and padding preserves the first gate and the function. In the reverse direction, every choice of the 62 encoded gates and final output is an admissible monotone circuit.

## Why 17 cases suffice

If a circuit of size at most 62 exists, choose one of minimum size. Suppose its first gate is AND(i, j) for a nonedge of distinct vertices. Replace the gate output by false at every use. On each minimal true input (the endpoints of one edge), the original first gate already evaluates to false. The modified circuit therefore still accepts every edge input. It is monotone, so it accepts every input containing an edge. Replacing a wire by false in a monotone circuit can only lower the output pointwise, so the modified circuit still rejects every independent set. Propagating the new constant removes the first gate and produces a strictly smaller circuit for the same function, contradicting minimality.

Thus a minimum circuit begins with OR, or with AND on an edge. The three edge-pair orbits have representatives (0, 17), (1, 14), and (2, 14). Orbit relabeling and output padding preserve the selected case. A SAT result in any retained case gives a circuit, and UNSAT certificates covering the 17 retained cases would exclude every size-at-most-62 circuit. An omitted diagnostic case can itself be SAT when extra gates are available.

## Verification

```sh
python3 solver/verify_encoding.py
```

Seven small solver checks use the optional system `libz3` shared library. On a single edge the one-gate AND case is SAT and the OR case is UNSAT. On the two-edge star, the OR of the leaves takes one more gate to meet the center. One gate is UNSAT, two gates are SAT with that first OR, two are UNSAT with a first AND of the leaves, and three are SAT by padding. At four gates the same star is SAT even with a first AND of its nonadjacent leaves, illustrating the distinction between an unnecessary case and an unsatisfiable case.

The target witness check reads `upper/Upper63.lean`, relabels its input wires by a graph automorphism, and sets all structure, prefix, and truth variables. The first gate becomes OR(1, 3), case 13. All 8,472,350 clauses at 63 gates are satisfied by the explicit assignment. This check requires only Python's standard library and can be run separately with `--target-only`. See `verification.json` for the recorded results.
