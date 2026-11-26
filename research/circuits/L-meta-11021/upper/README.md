# A 16-gate depth-five witness for L-meta-11021

The circuit selects the five star centers 0, 5, 6, 7 and 8. Their assigned neighbors are {4}, {0,1}, {2,3}, {0,2,4} and {1,3,4,6}, respectively. The stars partition all 12 edges. Combining the star tests gives a 16-gate AND/OR circuit of depth five.

`Upper.lean` proves `HasCircuitSize 9 target 16` and checks `starCircuit.depth 9 = 5` against the project definitions. From a prepared project Lean directory, run `lake env lean /absolute/path/to/Upper.lean`. The upper theorem uses the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. The depth evaluation uses only `propext`.

Run `python3 -B construct.py` and compare its output with `expected.txt`. The program enumerates the three five-vertex covers, assigns each edge to a selected endpoint in all 24 possible ways, and builds disjunctions by combining the two least-deep available wires first. It checks the resulting circuit against all 512 truth assignments.

The known unrestricted size lower bound of 16 also implies that no depth-four circuit computes this target. Unfold a fan-in-two output cone of depth at most four into an expression tree. At most 1 + 2 + 4 + 8 = 15 internal gates occur. Recompile these gates bottom-up, reusing the nine original inputs. Original zero-input gates remain gates. Any default-false read can continue to refer to an out-of-range wire. The recompiled circuit would have size at most 15. Thus the displayed witness attains both size and depth minima once the complementary unrestricted size bound is applied.

The unmodified project mathematical checker accepted this circuit as evidence for the explicit 16-gate size bound. A second call on the same compiled proof rejected a 15-gate bound for a statement mismatch. Run `bash replay-checker.sh /path/to/pequalnp-proofs/lean` from this folder. The wrapper derives both propositions from the posted negative statement. [Checker inputs](make-check.py) · [Replay](replay-checker.sh)
