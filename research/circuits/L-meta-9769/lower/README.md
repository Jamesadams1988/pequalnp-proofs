# Eight input restrictions give a 49-gate lower bound

For the 42-vertex, 104-edge graph of L-meta-9769, every fan-in-two AND/OR/NOT circuit needs at least **49 gates**. `Lower.lean` uses the project's unrestricted `HasCircuitSize` predicate. The assigned inequality would require at least 124 gates.

In order, fix the point inputs numbered `12, 11, 9, 7, 0, 3, 2, 1`. At every step the pinned function still depends on the input being fixed, and both choices of its value leave a nonconstant function. The project's two-gate elimination theorem therefore gives one branch whose circuit is smaller by at least two gates. After eight choices all 34 unpinned inputs remain essential, irrespective of the values chosen. Input support then requires 33 more gates. This gives `2 × 8 + 33 = 49`.

For each surviving input, the finite certificate supplies an adjacent witness. The low assignment sets only the witness to true before the previously fixed bits are applied. The high assignment additionally sets the tested bit to true. The low input rejects even when all prior pins are true, and the high input accepts even when all prior pins are false. Monotonicity of the target edge *function* gives the result for every pin assignment; the circuit computing the function can contain NOT gates. Lean checks both extreme assignments, each stage's rank identities, and the size of the terminal support using kernel reduction.

In a prepared checkout of the upstream Lean project, run `lake build +PEqualNP.MetaComplexity.Helpers.PermInputs` followed by `lake env lean /absolute/path/to/Lower.lean`. The source contains the graph, certificate, and exact desk edge predicate.
