# Six-input table 0xeeeaeae8eae8eae8

The minimum is **nine gates**, both over AND/OR/NOT and over AND/OR. Bit x of the table is the output on the six-bit assignment x, with variable i in bit i. This computational result establishes the positive companion of L-meta-12578 and rules out the negative statement.

## Replay

Use Python 3, Lean 4.36.0 and a CaDiCaL version with LRAT support. From this folder run:

```sh
python3 verify.py --output /tmp/12578-replay
```

The script accepts `--lean` and `--cadical` if these executables are outside PATH. It generates four UNSAT instances and their ASCII LRAT proofs, checks them using Lean's standard-library LRAT checker, and verifies a SAT positive control. The output directory needs about 100 MB with the tested solver. The included `ReplayFinite.lean` is the same standard-library driver used for the L-meta-3321 finite checks. It can also be run separately on the generated stems.

```sh
lean --run ReplayFinite.lean /tmp/12578-replay/u{4,5,6,7}
```

## Upper bound and controls

Write the inputs as a,b,c,d,e,f. Compute t=e∧f, u=d∧t, v=c∨u, w=b∧v, q=a∨w, r=b∨c, s=d∨t, z=r∨s, and output q∧z. The program compares its complete truth table to the target and checks that replacing the output AND by OR gives a different function.

All six variables are essential. The set {a,b} is both a minimal true support and a minimal zero certificate. Their intersection has size two. In a monotone read-once formula such sets meet in exactly one variable, by induction using the disjoint variables of the two subtrees. The witness uses t in two gates.

## Lower bound

Setting f=true yields the five-variable table 4008372968. This substitution saves at least one gate in any realization of the six-variable function. The output depends on all six inputs, so there is a gate with an effective occurrence of f. For AND or OR, substituting a constant either forces the resulting gate or reduces it to a wire. For NOT the substitution forces a constant. Propagate constants and bypass the affected gate. The remaining function depends on all five remaining variables and requires no standalone constant output. This argument allows arbitrary fan-out.

In a minimum circuit for the resulting cofactor, remove unused gates and bypass unary AND/OR, repeated-operand AND/OR, and constant gates. In Lean, an empty AND is true, an empty OR is false, and NOT negates its first operand, ignoring additional operands and returning true on an empty list. A missing wire, including a forward reference or missing output, reads false, which is handled by the same constant propagation. A circuit for this nonconstant, five-essential-input function can therefore use binary AND/OR on two distinct earlier wires and unary NOT. All gates are reachable and the last gate is the output.

The connected dependency graph of g gates and five essential inputs has at least g+4 edges and at most 2g edges, so g≥4. For each g from four through seven the program constructs a CNF that considers every normalized gate choice. It constrains one value per wire on **all 32 assignments**, enforces exactly one legal operation and operand choice per gate, and requires each non-output wire to be used. It permits arbitrary sharing. Among the topological orderings choose the lexicographically least sequence of (first operand, second operand, operation) triples. Two adjacent independent gates cannot be in descending order, since swapping them would decrease the sequence at its first changed triple. This justifies the order clauses.

All four CNFs are UNSAT. The size-eight positive control reconstructs a monotone circuit from the solver model, checks every CNF clause, and compares the decoded circuit against the full cofactor truth table. Consequently the cofactor minimum is eight and the saving under f=true gives the original lower bound of nine. The LRAT replay certifies the generated CNFs. The normalization and encoding arguments above connect those CNFs to the circuit-size statement.
