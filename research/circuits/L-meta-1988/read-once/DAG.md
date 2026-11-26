# A 31-gate lower bound for the stored circuit

The read-once cover theorem gives an unrestricted lower bound of 31 for the circuit preceding the terminal AND in L-meta-1988. The proposed bound of 63 remains open. The same argument forces seven distinct shared wires in the augmented output cone.

## Decomposition by shared wires

Consider a single-output acyclic AND/OR circuit. Trim to the ancestors of the output. An argument occurrence of a gate counts as one use of the supplying wire. Two occurrences in one argument list count twice. A shared wire is a nonconstant input or gate output used at least twice in this cone. Here one can conservatively count every gate output, including a gate whose value is constant. Immediate constant arguments can be used freely. A read-once formula may use constants and may use each original variable at most once.

If the cone has h shared wires, its output is the conjunction of at most 2ʰ read-once formulas. With h = 0, recursive expansion is already read-once. If h > 0, take the earliest shared wire u in topological order, with inputs before gates. Every strict ancestor of u has only one use in the cone. Its only path out leads to u. Thus u computes a read-once formula g, and every variable occurring in g reaches the rest of the cone only through u. For u itself an input, g is that single variable.

Replace all uses of u by an immediate constant 0 or 1 to obtain output functions f₀ and f₁. Trim unused ancestors again. Each new cone has at most h−1 shared wires, since substitution creates no additional uses of a remaining wire. Both cofactors use variables disjoint from g. Upward monotonicity in the substituted wire gives f₀ ≤ f₁, and the original function satisfies

```
f = f₁ AND (g OR f₀).
```

Apply the induction hypothesis to the two cofactors. Keep the read-once factors for f₁. For every read-once factor q for f₀ add the factor g OR q. Distributivity gives exactly f, and g and q have disjoint variables. This uses at most 2ʰ⁻¹ + 2ʰ⁻¹ factors. In particular a circuit with at most six shared wires has at most 64 factors. The integer certificate requires at least 69, so h ≥ 7.

For two terminal operands whose cones have h₁ and h₂ shared wires, taking the union of the two factor lists similarly gives 2ʰ¹ + 2ʰ² ≥ 69. At least one operand therefore has six shared wires within its own cone. The argument also applies to raw-variable restrictions. If every cofactor obtained by fixing r chosen variables is read-once, each assignment Z of the chosen variables gives a read-once factor consisting of f restricted to Z OR the disjunction of variables fixed to zero by Z. Their conjunction equals f and has at most 2ʳ factors. Consequently there cannot be a set of at most five such raw variables for each of the two operands.

## Application to the project's wire convention

For the 26 inputs, gate number j sees only indices below 26+j. Replace every larger index in that gate's argument list by a private immediate false constant, exactly as the evaluation fold's default read does. A zero-argument AND is true and a zero-argument OR is false. Unary gates copy their operand. All of these operations remain monotone and have at most two argument occurrences. A repeated reference to an existing wire contributes two parallel uses. Invalid references and repeated references can be left in place under these conventions.

Append one virtual AND whose argument list is the assigned list of wire indices, of length at most two. Its reads come from the completed list of wires, again with default false. This implements the tested function on the nose and uses at most C.size + 1 gates. The stored C.output value is irrelevant because the assignment uses the separate list of terminal wires. Appending this gate also handles an empty list, a singleton list and two equal indices uniformly.

Trim to this virtual gate and its ancestors. Every original variable is essential: choose an adjacent vertex w and test {w} and {v,w} to witness the change in variable v. Consequently all 26 raw input nodes remain. Let g be the number of gate nodes in this trimmed cone, counting the virtual root. Count only argument occurrences supplied by an actual input or gate node. Immediate false constants need no vertices or arcs. Zero-input gate outputs, including original constant gates, are ordinary vertices when used. Let E be the resulting number of directed arcs with multiplicity.

All nodes except the root have an outgoing arc. Each of at least seven shared wires has a second outgoing arc. Hence E ≥ 26 + g − 1 + 7. Every gate has at most two inputs, so E ≤ 2g. Together these bounds give g ≥ 32. Since g ≤ C.size + 1, the stored size is at least 31.

Lean verifies the monotone Shannon identity and proves that the recursively specified splits produce at most 2ʰ read-once factors. A second Lean file proves the implication from the factor-count and outdegree inequalities to the seven-wire and 31-gate conclusions. The construction of the split certificate from an arbitrary stored circuit, the correspondence with the project’s gate representation, and the finite capacity computation are covered by the argument and replay above. [Factor decomposition](../support/SplitCover.lean) · [Cone counting](../support/ConeCount.lean) · [Capacity replay](check.cpp)

## Limit of the factor count

The integer cover optimum lies between 69 and 96. The explicit upper certificate `cover96.txt` contains the 26-bit accepted-singleton masks of 96 canonical factors. Run `python3 -B check_cover.py` to verify them on every one of the 52 minimal true and 704 maximal false assignments. The fractional cover certificate in the sibling `../fractional/` shows that no nonnegative weighting of the 704 negatives can improve 69. Even the exact integer cover optimum cannot raise the seven-wire lower bound via the inequality 2ʰ alone, because 96 ≤ 128.
