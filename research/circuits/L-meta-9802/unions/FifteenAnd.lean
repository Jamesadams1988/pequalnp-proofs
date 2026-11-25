import UnionData
import MaskFamily

namespace Row9802
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Every circuit for the listed 95-edge function has at least 15 binary AND gates. -/
theorem fifteenAnd (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x : Fin 40 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 40, (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true) :
    15 ≤ C.gates.countP Signature.binaryAnd := by
  have h := MaskFamily.blockBound Unions.all C hm computes
  by_contra small
  have bound : C.gates.countP Signature.binaryAnd ≤ 14 := by omega
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) bound
  omega

end Row9802
#print axioms Row9802.fifteenAnd
