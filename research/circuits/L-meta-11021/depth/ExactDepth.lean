import DepthJoin
import ExactLower

namespace CircuitTable11021
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The least fan-in-two AND/OR/NOT circuit depth of the nine-vertex predicate is five. -/
theorem minimumDepth :
    IsLeast {d : ℕ | ∃ C : Circuit, FanInTwo C ∧ circuitFun 9 C = target ∧ C.depth 9 = d} 5 :=
  target_depth_of_lower positive

#print axioms minimumDepth
end CircuitTable11021
