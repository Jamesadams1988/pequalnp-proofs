# Nineteen states for simultaneous read-2 on one input pair

Fix two distinct inputs x and y. For a wire, ask whether it has a proof tree using only x and y, with at most two copies of each. The smallest deterministic gate evaluator that answers this question on every constant-free binary AND/OR formula has exactly **19 states**. The same evaluator runs once per gate on a circuit DAG because each gate's state is a function of its two input states.

## The states

Write (a,b) for a proof tree's numbers of x and y leaves. An x-input contributes (1,0), a y-input contributes (0,1), and any other input contributes no feasible tree. OR takes the union of its child count sets. AND adds one vector from each child. Thus any vector with a coordinate greater than two may be discarded permanently. Any vector dominated coordinatewise by another feasible vector can also be discarded. The remaining antichain records exactly which budgets (i,j) in the 3-by-3 grid admit a tree.

Equivalently, record the least feasible y-budget at x-budgets 0, 1, and 2, using 3 if no y-budget works. The resulting triple is weakly decreasing with entries in {0,1,2,3}. There are 20 such triples. Only (0,0,0) is excluded because a tree in the binary constant-free model has at least one leaf. Every other profile is realizable. For each minimal pair in its grid, AND the prescribed number of x and y copies, then OR the resulting terms. The empty grid is realized by x AND x AND x, with binary parentheses.

## Distinguishing all states

If two profiles differ at budget (i,j), append 2−i x-leaves and 2−j y-leaves by successive binary AND gates. The resulting expression accepts at budget (2,2) exactly when the original wire accepted at (i,j). No new gate is needed when both counts are zero. This supplies one of nine fixed continuations for each of the 171 unordered pairs of profiles. Any evaluator assigning the same state to two such wires would give identical answers in their distinguishing continuation.

## Replay and scope

Run `python3 replay.py` to generate the profiles by gate closure and check all 171 separations. Run `lake env lean /path/to/PairAlgebra.lean` from the project's Lean directory with its pinned Lean 4.36.0 toolchain. The theorem `FixedPairAlgebra.exact_state_count` constructs a 19-state evaluator and injects 19 explicitly realized wires into the state type of any exact finite deterministic evaluator. It uses the standard library axioms `propext`, `Classical.choice`, and `Quot.sound`.

The observation is the joint budget predicate used by `ReadK.readsAtMost` for the chosen pair. The official count recursion caps overflowing counts at three. Discarding those vectors gives the same observations since every subsequent count change is an addition of nonnegative counts. At a prime implicant pair, each accepting tree must include both variables. A proof tree at an intermediate wire may include only one. The lower bound quantifies over intermediate-wire evaluators with arbitrary formula continuations. It gives neither a gate-count bound for incidence nor a size-preserving conversion of a circuit to read-2.
