import Lower38
import FifteenAnd

namespace Row9802
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Row4201.Charging

private theorem countKinds (gs : List Gate) :
    gs.countP isOr + gs.countP Signature.binaryAnd ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases h : g.op <;>
      simp [List.countP_cons,isOr,Signature.binaryAnd,h] <;> first | omega | (split <;> omega)

/-- Standard-axiom total lower bound, with arbitrary fan-in-two monotone wiring. -/
theorem lower53 (C : Circuit) (hm : Monotone2 C) (computes : ∀ x : Fin 40 → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 40,
      (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true) : 53 ≤ C.size := by
  exact (Nat.add_le_add (Connected.lower38 C hm computes) (fifteenAnd C hm computes)).trans
    (countKinds C.gates)

/-- The extra OR charge uses the independently certified native six-cycle exclusion. -/
theorem lower54 (C : Circuit) (hm : Monotone2 C) (computes : ∀ x : Fin 40 → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 40,
      (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true) : 54 ≤ C.size := by
  exact (Nat.add_le_add (SixCycle.lower39 C hm computes) (fifteenAnd C hm computes)).trans
    (countKinds C.gates)

end Row9802
#print axioms Row9802.lower53
#print axioms Row9802.lower54
