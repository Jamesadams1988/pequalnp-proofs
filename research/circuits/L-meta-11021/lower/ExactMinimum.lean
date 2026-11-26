import ExactLower
import UpperJoin

namespace CircuitTable11021
open PEqualNP.MetaComplexity

theorem exactMinimum : IsLeast {t : ℕ | HasCircuitSize 9 target t} 16 :=
  minimumOfLower positive

#print axioms exactMinimum
end CircuitTable11021
