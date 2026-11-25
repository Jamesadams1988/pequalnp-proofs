# Six-cycle OR-count certificates

The six-cycle edge function returns true when the selected vertices contain one of the cyclic edges 01, 12, 23, 34, 45, 50. Its minimum is five binary OR gates when conjunctions are free. In the accompanying induced-plane coordinates, cyclic vertices 0 through 5 correspond to local indices 0, 3, 2, 5, 1, 4.

Run the following from this directory. The replay uses Python 3 and its standard library.

```sh
python3 verify.py
```

The verifier regenerates all 1,509 DIMACS clauses on 419 variables and compares the result byte for byte with `cycle6-4.cnf.gz`. It checks all 10,070 reverse-unit-propagation additions in the CaDiCaL LRAT certificate, including the final empty clause. It also evaluates the explicit five-OR circuit in `cycle6-5.json` on all 64 assignments.

For the lower bound, each of four OR gates takes two conjunctions of selected primary inputs and earlier OR outputs. The final output is a conjunction of selected wires. Any monotone circuit can be put in this form by retaining its OR gates in topological order and flattening the intervening conjunctions. Constant signals may be propagated and unary gates bypassed before flattening. A nonconstant output then uses nonempty selectors throughout. Additional unused OR gates pad a circuit with fewer than four ORs. Swapping the operands at each OR permits the encoded lexicographic ordering. The CNF constrains the six minimal true assignments and all five maximal false assignments. Monotonicity fixes the function on all remaining assignments.

This independent replay checks the finite SAT encoding and witness. The accompanying Lean development records its own formal normalization and reflection status.
