import PEqualNP.Defs

namespace CircuitTable11031
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)

def starCircuit : Circuit :=
  ⟨[⟨.or, [0, 7]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [13, 2]⟩,
    ⟨.and, [6, 14]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [16, 8]⟩,
    ⟨.and, [7, 17]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 19]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [21, 15]⟩,
    ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩], 24⟩

theorem upper : HasCircuitSize 9 target 16 := by
  refine ⟨starCircuit, ?_, by decide, ?_⟩
  · simp [starCircuit, FanInTwo]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, starCircuit, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

end CircuitTable11031
