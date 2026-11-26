# A three-gate change isolates read-2 failure to one point-star

Let the graph be simple and bipartite. Assume every point has at least one incident line, and form the point-star circuit by setting Yₚ to the OR of the inputs for its incident lines and Aₚ to xₚ AND Yₚ. OR all the Aₚ to obtain the output. Keep one chosen Aₚ wire and replace its contribution to the output with three new gates.

1. Compute B = xₚ OR Yₚ.
2. Compute C = Aₚ AND B.
3. Use D = Aₚ AND C at the output in place of Aₚ.

**Boolean semantics.** D has the same Boolean value as Aₚ for any values of the two operands. Substitution preserves the incidence function on every assignment. The original Aₚ and Yₚ wires are shared in the ordinary circuit DAG. Every new gate reads exactly two earlier wires.

**Proof counts.** On an incident pair (r,l), only star r can produce a proof tree supported on those two wire inputs. If r is unmodified, the point input and the unique selected line occurrence in Yᵣ give counts (1,1). If r is the modified point, the two independent occurrences of Aₚ contribute (2,2). B permits either one point leaf or one line leaf. The only possible total counts are (3,2) and (2,3). Thus both scalar minima equal two, while the least simultaneous bound is three. No nonincident pair can support an output proof. The same reasoning applies to any chosen collection of distinct point-stars, with failure precisely on edges incident to those points.

**Gate budget.** For N points, each of degree q+1, the original circuit uses Nq line-OR gates, N AND gates and N−1 output-OR gates, for N(q+2)−1 gates. Changing one star gives N(q+2)+2 gates and exactly q+1 bad incident pairs. Changing s stars adds exactly 3s gates and produces s(q+1) bad pairs. These are sizes of the displayed constructions.

## Fano certificate

The point and line labels are the seven nonzero binary triples interpreted as the integers 1 through 7. Incidence means their binary dot product is zero. Zero-based index 0 corresponds to integer 1. The chosen point's incident line indices are 1, 3 and 5.

The standard circuit has 27 gates and the localized variant has 30. Python compares the two with the defining incidence predicate on all 16,384 assignments. The function is true on 15,926. It evaluates full uncapped proof count sets on all 49 possible pairs. All 21 incident pairs pass the scalar threshold. Eighteen pass the joint threshold. The three selected pairs fail and all 28 nonincident pairs give empty sets.

Lean checks both circuits against the pinned upstream binary AO2 predicate, their sizes, and the Boolean identity of the local gadget. For each of the 21 incident pairs it checks the original joint result and both localized tests directly against the upstream functions. Python checks the explicit Lean gates and theorem statements match its generated instance. [Upstream read definitions](https://github.com/open-goat/pequalnp-proofs/blob/1972ec9f567e2b3c90b0adc5472172f7e5ddfab0/lean/PEqualNP/Defs/ReadK.lean)

Reproduce with Python 3.10 or later. For Lean, build PEqualNP.Defs in the pinned upstream checkout at 1972ec9f567e2b3c90b0adc5472172f7e5ddfab0, then use its lake environment.

```sh
python3 localized.py | diff - results.txt
# From the upstream lean/ directory
lake env lean /path/to/LocalizedFano.lean
```
