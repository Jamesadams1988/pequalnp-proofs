# A checked 54-gate circuit for L-meta-9791

Research by James Adams (Jamesadams1988).

The project asks whether 53 binary AND/OR gates suffice to recognize an edge in a particular 24-vertex graph. Its desk described a computed 54-gate construction. Here is a kernel-checked witness at 54, a sharp lower bound for one class of formulas, and a way to transfer proposed circuits to the full projective plane of order three. The unrestricted 53-gate question remains open in this work. [Desk entry](https://pequalnp.com/desk/step?gap=L-meta-9791)

## Where the 54 gates go

For each of the 11 line vertices, three OR gates combine its four neighboring point inputs. One AND gate tests whether that line and a neighboring point are both selected. Ten more OR gates combine the 11 results. This uses 33 + 11 + 10 = 54 gates. The Lean proof compares the circuit's symbolic monotone disjunctive normal form with the 44 edges for every input. The project's local checker accepted the relaxed bound and rechecked 1,730 project declarations. Running the same file against the original bound of 53 produced a statement mismatch. [Witness](Control54.lean) · [Machine-readable gates](Control54.json) · [Local checker source](https://github.com/open-goat/pequalnp-proofs/blob/e125f04d0dc6fed67cee48a1d06692912e167c32/tools/check-lean.mjs)

Suppose a formula separately builds blocks of the form “some point from this set AND some line from that set”, then ORs the blocks together. Each block must consist entirely of edges. The graph has no four-cycle, so every nonempty block is a star. Building a star costs one gate per edge it covers. The graph contains a matching of 11 edges and a single star covers at most one of them. The blocks therefore cost at least 44 gates, and joining them costs at least 10 more. Lean proves this for any such cover, even when blocks overlap or repeat, and checks that the column construction attains 54. A search for 53 can exclude this entire family of unshared formulas. [Flat-cover definitions and proofs](Flat.lean)

## Restoring the two missing lines

Write the point coordinates modulo 13. Line coordinate w has neighbors w + {0, 1, 3, 9}. The eleven desk line inputs 13 through 23 correspond to w = 2 through 12. Reinstating w = 0 and w = 1 adds eight edges. The extension constructs those two missing stars and combines them with the original output using ten new gates. Nine gates precede the original gates, whose wire references are renumbered. The final OR reads the two outputs. This preserves the project's semantics even for out-of-range references.

For either choice of marked inputs (points or lines), the project's syntactic degree adds at AND gates and takes the maximum at OR gates. The extension takes output degree d to max(1, d). A 53-gate solution would therefore give a 63-gate full-plane circuit. Applying the full-plane results contributed by rifter0418 and willakone gives a search restriction for the original graph. Every qualifying 53-gate circuit must have syntactic output degree at least two on both sides. [Combined degree bound](DegreeBounds.lean) · [Extension](Extension.lean) · [Line-degree bound](https://github.com/open-goat/pequalnp-proofs/blob/e125f04d0dc6fed67cee48a1d06692912e167c32/lean/PEqualNP/Outside/L_meta_1500.lean#L4503) · [Point-degree bound](https://github.com/open-goat/pequalnp-proofs/blob/e125f04d0dc6fed67cee48a1d06692912e167c32/lean/PEqualNP/Outside/L_meta_2145.lean#L5220)

## Replay the checks

From this folder, run `python3 check_circuit.py`. It compares all 16,777,216 input assignments against the explicit edge list. Pass a candidate JSON filename to test another topologically ordered binary AND/OR circuit. Wires 0 through 23 are inputs. Subsequent wires name gates in list order, and `output` names the result wire. On disagreement it prints a counterexample and exits with status 1.

The Lean sources use Lean 4.36.0 and the project's dependencies at `e125f04d0dc6fed67cee48a1d06692912e167c32`. Set `research_dir` to this folder's absolute path. In a prepared project checkout, run these commands from the repository root. The two full-plane dependencies are substantial and can be built in sequence. The final command invokes the official checker for the 54-gate statement.

```sh
(cd lean && lake env lean "$research_dir/Flat.lean")
scratch=$(mktemp -d)
(cd lean && lake build +PEqualNP.Outside.L_meta_1500 && lake build +PEqualNP.Outside.L_meta_2145)
(cd lean && lake env lean -j1 -R "$research_dir" -o "$scratch/Extension.olean" "$research_dir/Extension.lean")
(cd lean && lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean -j1 "$2/DegreeBounds.lean"' sh "$scratch" "$research_dir")
cp "$research_dir/Control54.lean" lean/PEqualNP/Outside/L_meta_9791_control54.lean
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_9791_control54.lean "$research_dir/Bound54.txt" check
```
