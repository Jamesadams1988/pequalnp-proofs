import DepthBound
import Upper

namespace CircuitTable11021
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem target_depth_of_lower (low : ∀ t : ℕ, HasCircuitSize 9 target t → 16 ≤ t) :
    IsLeast {d : ℕ | ∃ C : Circuit, FanInTwo C ∧ circuitFun 9 C = target ∧ C.depth 9 = d} 5 := by
  constructor
  · refine ⟨starCircuit, by simp [starCircuit, FanInTwo], ?_, depth_five⟩
    funext x
    change starCircuit.eval (List.ofFn x) = target x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, starCircuit, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl
  · rintro d ⟨C, hC, heq, hd⟩
    by_contra! h
    have hsmall := DepthSize.size_of_depth_four (n := 9) C hC (by omega)
    rw [heq] at hsmall
    exact (by decide : ¬ 16 ≤ 15) (low 15 hsmall)

#print axioms target_depth_of_lower
end CircuitTable11021
