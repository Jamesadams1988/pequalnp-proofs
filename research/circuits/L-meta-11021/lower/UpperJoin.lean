import CaseAudit
import Upper

namespace CircuitTable11021
open PEqualNP.MetaComplexity

theorem minimumOfLower (h : ∀ t : ℕ, HasCircuitSize 9 target t → 16 ≤ t) :
    IsLeast {t : ℕ | HasCircuitSize 9 target t} 16 :=
  ⟨upper, fun _ ht => h _ ht⟩

#print axioms minimumOfLower
end CircuitTable11021
