import CoreTransfer
import EmbeddedFive

/-! The finite four-OR exclusion is an explicit hypothesis. This transfer
does not import the tactic or certificate used to discharge that exclusion. -/
namespace Row4201
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fortyOneOfNoFour (reject : ∀ p : HexFour.Program, ¬ HexFour.agrees p)
    (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔ PGSequence.accepts x) :
    41 ≤ C.gates.countP Charging.isOr := by
  apply liftCycle (b := 5) _ C hm computes
  intro D hd evalD
  have bound := HexNormalize.embeddedFive reject D hd evalD
  have names : ZeroSensitivity.isOr = Charging.isOr := by
    funext g
    unfold ZeroSensitivity.isOr Charging.isOr
    cases g.op <;> rfl
  rwa [names] at bound

end Row4201
#print axioms Row4201.fortyOneOfNoFour
