import PEqualNP.Defs.MetaComplexityMinimal

namespace FirstWire17336
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)

private theorem inputs (x : Fin 9 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl

def Meets (C : Circuit) (s : Nat) (first : (Fin 9 → Bool) → Bool) : Prop :=
  FanInTwo C ∧ C.size = s ∧
    (∀ x, (C.wires (List.ofFn x)).getD 9 false = first x) ∧
    circuitFun 9 C = target

def not5 : Circuit :=
  ⟨[⟨.not, [5]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 8]⟩,
    ⟨.and, [1, 14]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 16]⟩,
    ⟨.or, [2, 4]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [3, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [22, 17]⟩,
    ⟨.or, [23, 19]⟩, ⟨.or, [24, 21]⟩], 25⟩

theorem not5_spec : Meets not5 17 (fun x => !(x 5)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [not5, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, not5, GateOp.eval, List.getD]
  · funext x
    change not5.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, not5, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def and5_6 : Circuit :=
  ⟨[⟨.and, [5, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 8]⟩,
    ⟨.and, [1, 14]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 16]⟩,
    ⟨.or, [2, 4]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [3, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [22, 17]⟩,
    ⟨.or, [23, 19]⟩, ⟨.or, [24, 21]⟩], 25⟩

theorem and5_6_spec : Meets and5_6 17 (fun x => (x 5 && x 6)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [and5_6, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, and5_6, GateOp.eval, List.getD]
  · funext x
    change and5_6.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, and5_6, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def and5_7 : Circuit :=
  ⟨[⟨.and, [5, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 8]⟩,
    ⟨.and, [1, 14]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 16]⟩,
    ⟨.or, [2, 4]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [3, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [22, 17]⟩,
    ⟨.or, [23, 19]⟩, ⟨.or, [24, 21]⟩], 25⟩

theorem and5_7_spec : Meets and5_7 17 (fun x => (x 5 && x 7)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [and5_7, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, and5_7, GateOp.eval, List.getD]
  · funext x
    change and5_7.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, and5_7, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def and5_8 : Circuit :=
  ⟨[⟨.and, [5, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 8]⟩,
    ⟨.and, [1, 14]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 16]⟩,
    ⟨.or, [2, 4]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [3, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [22, 17]⟩,
    ⟨.or, [23, 19]⟩, ⟨.or, [24, 21]⟩], 25⟩

theorem and5_8_spec : Meets and5_8 17 (fun x => (x 5 && x 8)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [and5_8, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, and5_8, GateOp.eval, List.getD]
  · funext x
    change and5_8.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, and5_8, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_6 : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [0, 10]⟩,
    ⟨.or, [5, 7]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩], 24⟩

theorem or5_6_spec : Meets or5_6 16 (fun x => (x 5 || x 6)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_6, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_6, GateOp.eval, List.getD]
  · funext x
    change or5_6.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_6, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_6Padded : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [0, 10]⟩,
    ⟨.or, [5, 7]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩, ⟨.or, [24, 24]⟩], 25⟩

theorem or5_6Padded_spec : Meets or5_6Padded 17 (fun x => (x 5 || x 6)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_6Padded, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_6Padded, GateOp.eval, List.getD]
  · funext x
    change or5_6Padded.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_6Padded, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_7 : Circuit :=
  ⟨[⟨.or, [5, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [12, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩], 24⟩

theorem or5_7_spec : Meets or5_7 16 (fun x => (x 5 || x 7)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_7, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_7, GateOp.eval, List.getD]
  · funext x
    change or5_7.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_7, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_7Padded : Circuit :=
  ⟨[⟨.or, [5, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [12, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩, ⟨.or, [24, 24]⟩], 25⟩

theorem or5_7Padded_spec : Meets or5_7Padded 17 (fun x => (x 5 || x 7)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_7Padded, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_7Padded, GateOp.eval, List.getD]
  · funext x
    change or5_7Padded.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_7Padded, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_8 : Circuit :=
  ⟨[⟨.or, [5, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [12, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩], 24⟩

theorem or5_8_spec : Meets or5_8 16 (fun x => (x 5 || x 8)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_8, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_8, GateOp.eval, List.getD]
  · funext x
    change or5_8.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_8, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

def or5_8Padded : Circuit :=
  ⟨[⟨.or, [5, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 17]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [12, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩, ⟨.or, [24, 24]⟩], 25⟩

theorem or5_8Padded_spec : Meets or5_8Padded 17 (fun x => (x 5 || x 8)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [or5_8Padded, FanInTwo]
  · intro x
    rw [inputs]
    simp [Circuit.wires, or5_8Padded, GateOp.eval, List.getD]
  · funext x
    change or5_8Padded.eval (List.ofFn x) = target x
    rw [inputs]
    simp [Circuit.eval, Circuit.wires, or5_8Padded, GateOp.eval, List.getD, target,
      Bool.and_or_distrib_left]
    ac_rfl

#print axioms not5_spec
#print axioms and5_6_spec
#print axioms and5_7_spec
#print axioms and5_8_spec
#print axioms or5_6_spec
#print axioms or5_6Padded_spec
#print axioms or5_7_spec
#print axioms or5_7Padded_spec
#print axioms or5_8_spec
#print axioms or5_8Padded_spec

end FirstWire17336
