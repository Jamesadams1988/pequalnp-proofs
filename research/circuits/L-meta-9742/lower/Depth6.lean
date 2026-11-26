import Elimination
import DepthBound

namespace Plane9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Elimination (V edgePairs target)

/-- Fan-in-two AND/OR/NOT circuits for the 51-edge predicate have output depth at least six. -/
theorem depth_six (C : Circuit) (hfan : FanInTwo C)
    (hc : ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : V, (u.val,v.val) ∈ edgePairs ∧ x u = true ∧ x v = true) :
    6 ≤ C.depth 26 := by
  have correct : circuitFun 26 C = target := by
    funext x
    exact Bool.eq_iff_iff.mpr ((hc x).trans (Elimination.hits x).symm)
  by_contra! short
  have small : HasCircuitSize 26 (circuitFun 26 C) 31 :=
    DepthSize.size_of_depth (d := 5) C hfan (by omega)
  rw [correct] at small
  exact (by decide : ¬ 32 ≤ 31) (Elimination.lower 31 small)

#print axioms depth_six
end Plane9742
