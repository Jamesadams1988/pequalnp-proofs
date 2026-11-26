# Sharp first-gate bounds for individually safe products

Let the function be the OR of the 12 edges listed in L-meta-17336. Consider circuits for which every gate reaching the output belongs to the following three stages. The first stage builds disjunctions of signed input literals with shared OR gates. The second contains AND products of two such factors. Each individual product implies the target on every assignment. The final stage can use binary AND/OR or unary NOT on these product outputs alone. Count every gate, including literal negations and disconnected gates. The desk fixes the value of the first wire even if the output never uses it.

| First wire | Minimum gates in this model | Optimal five-star orientations using that first gate |
|---|---:|---:|
| NOT 5 | 17 | 0 |
| 5 AND 6 | 17 | 0 |
| 5 AND 7 | 17 | 0 |
| 5 AND 8 | 17 | 0 |
| 5 OR 6 | 16 | 6 |
| 5 OR 7 | 16 | 4 |
| 5 OR 8 | 16 | 4 |

**Why every useful product is a star.** On any satisfying assignment, choose one true literal from each factor. If fewer than two distinct positive variables are selected by the two choices, one can satisfy both using at most one positive vertex, which violates product safety. Consequently the two chosen literals are the ends of an edge. Erasing negative literals preserves the product. Its two positive supports are disjoint, with all cross pairs edges. This graph has no four-cycle, so one support must contain just one vertex, the center. This argument applies even though the graph contains a triangle.

**Why 16 gates are necessary.** If there are k distinct reachable nonempty products, their centers cover the edges. Indeed, on the assignment selecting the two ends of an edge, some product must change from its value on the empty assignment. The graph has minimum vertex cover five. For each center c, let r be its number of products and d the number of distinct leaves they cover. Their operand disjunctions require at least d−r OR gates: adding r−1 ORs would connect all d inputs to one output. ORs with two distinct positive inputs cannot help two different centers, since this would give them two common neighbors. Bypassing operands with at most one positive input in this counting argument avoids charging them twice. Summing gives at least 12−k preprocessing ORs, k products and k−1 binary postprocessing gates. The total is at least 11+k ≥16. [Earlier shared-gate argument](https://github.com/Jamesadams1988/pequalnp-proofs/tree/34ca6195b433a771e00e3980f5129ec06515009f/research/circuits/L-meta-9769/search)

**What equality allows.** At 16 gates, all five centers are distinct, and the products partition the 12 edges. A duplicate edge would increase the sum of the leaf counts. Every gate is charged as a useful binary gate. A first raw AND must therefore be the complete product for a one-edge star. A first raw OR must combine two leaves of one star. Assigning each edge to its center enumerates the 20 orientations attaining five stars. None contains the (5,8) edge as a one-edge star, and (5,6) and (5,7) are nonedges. The three OR cases occur in the counts shown above. To attain 17 in the four other cases, prepend the required first gate to a 16-gate circuit and leave its output unused.

The Python replay checks all 4,096 edge orientations and verifies each emitted witness on all 512 inputs. The witnesses also give upper bounds for the unrestricted desk circuit model. The sharp lower bounds in the table require the three-stage assumptions above. [Literal assignment](statement.json) · [Replay](verify.py) · [Gate lists](witnesses.json)
