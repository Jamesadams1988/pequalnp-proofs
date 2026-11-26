import PEqualNP.Defs

namespace PlaneReadTwoControl

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.MetaComplexity

/-- The polynomial of this circuit is xy(x+y)xy. -/
def four : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩, ⟨.and, [2, 4]⟩], 5⟩

/-- This circuit produces xy(xx+yy). -/
def five : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [0, 0]⟩,
  ⟨.and, [1, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩], 6⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def pair : Finset (Fin 2) := {0, 1}

theorem four_model : TopForm.IsAO2 2 four ∧ four.size = 4 := by decide
theorem five_model : TopForm.IsAO2 2 five ∧ five.size = 5 := by decide

theorem four_boolean : ∀ x : Fin 2 → Bool, circuitFun 2 four x = (x 0 && x 1) := by decide
theorem five_boolean : ∀ x : Fin 2 → Bool, circuitFun 2 five x = (x 0 && x 1) := by decide

theorem four_prime : IsPrimeImplicant 2 four pair := by decide
theorem five_prime : IsPrimeImplicant 2 five pair := by decide
theorem four_only_prime : ∀ S : Finset (Fin 2), IsPrimeImplicant 2 four S ↔ S = pair := by decide
theorem five_only_prime : ∀ S : Finset (Fin 2), IsPrimeImplicant 2 five S ↔ S = pair := by decide

theorem four_distinct_inputs : ∀ g ∈ four.gates, g.inputs.Nodup := by decide
theorem four_scalar : eachReadsAtMost four 2 [0, 1] 2 = true := by decide
theorem four_separate_minima :
    (scalarMults four 2 [0, 1] 0).getD four.output none = some 2 ∧
    (scalarMults four 2 [0, 1] 1).getD four.output none = some 2 := by decide
theorem five_scalar : eachReadsAtMost five 2 [0, 1] 1 = true := by decide
theorem five_separate_minima :
    (scalarMults five 2 [0, 1] 0).getD five.output none = some 1 ∧
    (scalarMults five 2 [0, 1] 1).getD five.output none = some 1 := by decide

theorem four_joint : readsAtMost four 2 [0, 1] 2 = false ∧
    readsAtMost four 2 [0, 1] 3 = true := by decide
theorem five_joint : readsAtMost five 2 [0, 1] 2 = false ∧
    readsAtMost five 2 [0, 1] 3 = true := by decide

theorem four_global : ¬ IsReadK 2 four 2 ∧ IsReadK 2 four 3 := by decide
theorem five_global : ¬ IsReadK 2 five 2 ∧ IsReadK 2 five 3 := by decide

#print axioms four_global
#print axioms five_global
#print axioms four_only_prime
#print axioms five_only_prime
#print axioms four_scalar
#print axioms five_scalar

end PlaneReadTwoControl
