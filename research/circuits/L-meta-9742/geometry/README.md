# Syntactic degree bounds for the 51-edge plane graph

The edges in L-meta-9742 are precisely the pairs (p,13+w) satisfying p−w ∈ {0,1,3,9} modulo 13, except for (0,13). Thus the displayed vertex labels already match the difference coordinates of the full-plane results. No permutation is needed.

## Degree at most one on one shore

Mark each point input with degree one and every line input with zero, or reverse the roles. The degree of an AND gate is the sum of its argument degrees, and that of an OR gate is their maximum. The degree discussed here is the syntactic degree at the designated output. Every correct circuit of degree at most one on either specified shore has size at least **62**.

Append a gate computing input 0 AND input 13, then OR this value with the old output. The resulting circuit computes the full projective-plane incidence function, costs exactly two additional gates, and has output degree equal to the maximum of one and the old degree on each shore. The full-plane line-degree lower bound L-meta-1500 and point-degree lower bound L-meta-2145 both require at least 64 gates. In particular any circuit with at most 61 gates for the listed graph would have degree at least two on both shores. The argument allows arbitrary nesting and gate reuse.

The file `Degrees.lean` proves the graph identity, legal extension, degree calculation and two one-shore lower bounds against the 51 literal edges. It also checks the edge count, absence of duplicate edges, the displayed matching, and the common-neighbor bound used below. It derives that the original output is in range from a true graph assignment, which prevents a formerly missing output index from acquiring a value after the extension. The inputs of earlier gates retain the project's default-false read semantics.

With Lean 4.36.0 and the project checkout, run from its Lean directory.

```sh
lake build +PEqualNP.Outside.L_meta_1500 +PEqualNP.Outside.L_meta_2145
lake env lean /path/to/Degrees.lean
```

## Degree at most one on both shores

Under the two simultaneous degree constraints the minimum is exactly **63**. This second bound has the following direct proof.

Prune gates outside the output cone, propagate constants and aliases, and replace degree-zero constant inputs by their actual values. These operations cannot increase either output degree. Within the resulting cone a wire's degree on a shore is positive precisely when its ancestor inputs include that shore. Each wire's degrees are bounded componentwise by those of the output. At any binary AND, its two nonconstant inputs therefore have disjoint nonempty sets of ancestral shores. One has only point ancestors and the other only line ancestors. The output of such an AND has positive degree on both sides and cannot enter any later binary AND. Its own two predecessor cones likewise contain only ORs. The entire function is thus an OR of point-line rectangle products. A pure OR bypass reaching the output would accept a singleton and cannot occur.

Every product is individually sound. Its rectangle is a star because any two distinct vertices on the same shore have at most one common neighbor. For a one-edge rectangle choose either endpoint as center. If there are k product gates, their star centers cover all edges. The perfect matching p = w+1 modulo 13 avoids the missing edge, hence k ≥ 13.

For each center v, let its stars use r distinct occurrences of leaf-side signals and let their supports cover a union of u neighboring vertices. Their pure OR subcircuits contain at least u−r gates. Indeed, contract all singleton-support copies; the union of ancestor cones has u inputs, at most r components, and at most two arcs into each gate. Every counted gate has a support of at least two neighbors of v and cannot be counted for another center. Summing over the centers costs at least 51−k pure OR gates, since these unions account for all 51 edges. There are also k product gates and at least k−1 further ORs connecting them to one output. The total is at least 51+k−1 ≥ 63. Computing the thirteen point stars and ORing their outputs attains 63 and satisfies both degree limits.

Consequently, any 62-gate candidate must have degree at least two on one shore. The one-shore transfer does not exclude a 62-gate candidate of degree one on just one shore, and these arguments do not establish the unrestricted 63-gate lower bound.
