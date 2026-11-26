# Two lower bounds for the 51-edge circuit

Lean proves that a fan-in-two monotone circuit for the listed edge function has at least **38 gates**. Allowing NOT still requires **32 gates**. The assigned target asks for 63 in the monotone model.

[Monotone.lean](Monotone.lean) specializes the general branch-count theorem L-meta-614 to all 51 ordered pairs in the assignment. There are no isolated vertices or equal neighborhoods, and every edge has alternative neighbors satisfying the theorem's condition. The 13 disjoint edges from point `p` to line `13 + ((p+4) mod 13)` witness a minimum vertex-cover size of 13, attained by the point shore. The theorem gives `26 + 13 ≤ C.size + 1`. Its final theorem uses the desk statement verbatim with the budget changed from 62 to 37. [Upstream theorem](https://github.com/open-goat/pequalnp-proofs/blob/51ff1cb1c0ec602ef4aeb60c50f25d37b917a035/lean/PEqualNP/Outside/L_meta_614.lean)

[Elimination.lean](Elimination.lean) checks a schedule with 18 input restrictions. Seven restrictions allow either bit and save two gates each. The other eleven fix false and save one gate each. Eight variables remain essential after every resulting branch, requiring seven further gates. This proves `14 + 11 + 7 = 32` without a monotonicity assumption. The finite witness checks and restriction induction specialize the fork's earlier L-meta-9769 and L-meta-1988 certificates.

With Lean 4.36.0, first build `PEqualNP.MetaComplexity.Helpers.PermInputs` and `PEqualNP.Outside.L_meta_614` in the project checkout. Compile the two modules in order from the project’s Lean directory, with `proofs` set to this folder’s absolute path.

```sh
out=$(mktemp -d)
lake env lean --root="$proofs" -o "$out/Elimination.olean" "$proofs/Elimination.lean"
lake env bash -eu -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$2" "$2/Monotone.lean"' -- "$out" "$proofs"
```

Both printed axiom reports list `propext`, `Classical.choice`, and `Quot.sound`.

[The standalone 38-gate checker module](checker/PEqualNP/Outside/ForkLower9742.lean) imports only L-meta-614 and inlines the complete edge list. [Checker statement](checker/lower.statement)

## Output depth

[Depth6.lean](Depth6.lean) proves output depth at least six, also allowing NOT. The depth-to-size construction turns any depth-five circuit into an equivalent circuit with at most 31 gates. The 32-gate unrestricted lower bound rules out that possibility.

Build the additional project dependency with `lake build PEqualNP.MetaComplexity.Helpers.Shannon`. To replay the depth proof after compiling Elimination, reuse the four generic modules in the adjacent fork package. [TreeBase.lean](../../L-meta-11021/depth/TreeBase.lean) · [Unfold.lean](../../L-meta-11021/depth/Unfold.lean) · [Emit.lean](../../L-meta-11021/depth/Emit.lean) · [DepthBound.lean](../../L-meta-11021/depth/DepthBound.lean)

```sh
generic="$proofs/../../L-meta-11021/depth"
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for name in TreeBase Unfold Emit DepthBound; do
    lean --root="$2" -o "$1/$name.olean" "$2/$name.lean"
  done
  lean --root="$3" "$3/Depth6.lean"
' -- "$out" "$generic" "$proofs"
```
