# A 51-gate lower bound for unrestricted circuits

Every fan-in-at-most-two AND/OR/NOT circuit for the 104-edge graph of L-meta-9769 has at least 51 gates. The assigned statement would require at least 124.

Begin by pinning point inputs 12, 11, 9, 7, 0, 3, 2, and 1 in this order. At each step, both choices leave a nonconstant function and the current input is essential. The project's two-gate elimination theorem guarantees a choice saving two gates. The first eight pins therefore save sixteen gates.

The three line inputs 25, 34, and 36 have no neighbors among these pinned points, regardless of their values. Fix the other eighteen line inputs to false. The graph on the remaining thirteen points and three lines comprises three degree-five line vertices with common point input 8. Each of the other twelve point inputs touches exactly one of these lines. Fix nine of them to false, keeping one private neighbor per line: point 4 for line 25, point 6 for line 34, and point 10 for line 36. The chosen value of each of these twenty-seven restrictions saves at least one gate.

Finally pin points 4 and 6 with the two-gate theorem. Whether each is set to true or false, the five inputs 8, 10, 25, 34, and 36 remain essential. For example, the unpinned third branch with point 10 permits point 8 to matter even when both previous private points are true. A circuit depending on five distinct inputs requires at least four gates. Adding the savings gives 16 + 27 + 4 + 4 = 51.

The Lean certificate supplies a neighbor witness for each live input at each stage. To verify all assignments to the flexible pins, it evaluates the low input with all flexible pins true and the high input with all flexible pins false. Monotonicity of the target edge function extends the dependence test to arbitrary intermediate pin assignments. The candidate circuit may contain NOT gates. The fixed-false elimination relabels inputs to apply the project's `gate_elim` theorem and restores the original arity. The flexible pins use `gate_elim_at`. The literal conclusion concerns the unrestricted `HasCircuitSize` from the assignment.

From the upstream checkout's Lean directory and pinned toolchain, run:

```sh
lake build +PEqualNP.MetaComplexity.Helpers.PermInputs
lake env lean /absolute/path/to/Terminal51.lean
```

The proof file includes the 104 edges, the literal formula, the complete schedule, and the finite witnesses.
