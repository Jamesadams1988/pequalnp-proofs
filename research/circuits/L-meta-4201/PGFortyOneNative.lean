import PGFortyOne
import HexFour

/-! Uses the finite four-OR exclusion verified by bv_decide's native LRAT checker. -/
namespace Row4201
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fortyOneNative (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔ PGSequence.accepts x) :
    41 ≤ C.gates.countP Charging.isOr :=
  fortyOneOfNoFour HexFour.noFour C hm computes

end Row4201
#print axioms Row4201.fortyOneNative
