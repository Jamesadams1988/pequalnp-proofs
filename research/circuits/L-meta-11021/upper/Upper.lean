import PEqualNP.Defs

namespace CircuitTable11021
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)

def starCircuit : Circuit :=
  ⟨[⟨.and, [0, 4]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [6, 12]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [4, 14]⟩,
    ⟨.and, [7, 15]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [8, 19]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [22, 23]⟩], 24⟩

theorem upper : HasCircuitSize 9 target 16 := by
  refine ⟨starCircuit, ?_, by decide, ?_⟩
  · simp [starCircuit, FanInTwo]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, starCircuit, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

theorem depth_five : starCircuit.depth 9 = 5 := by decide

#print axioms upper
#print axioms depth_five

end CircuitTable11021
