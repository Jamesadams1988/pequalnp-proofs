import ThresholdBatch

/-! Each explicit nine-gate AND/OR witness is evaluated on every assignment.
`ThresholdBatch` supplies the unrestricted lower bound by two essential pins.
-/
namespace FamilyExact
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CofactorBound

def ExactNine (f : BFn 6) : Prop :=
  Lower f 9 ∧ HasCircuitSize 6 f 9 ∧ ∃ C : Circuit, Monotone2 C ∧ C.size = 9 ∧
    ∀ x, C.eval (List.ofFn x) = f x

theorem fromWitness {f : BFn 6} (C : Circuit) (lower : Lower f 9)
    (hm : Monotone2 C) (hs : C.size = 9) (he : ∀ x, C.eval (List.ofFn x) = f x) :
    ExactNine f := by
  have fan : FanInTwo C := by
    intro gate hg
    obtain ⟨op, ar⟩ := hm gate hg
    exact ⟨op.elim Or.inl (fun ho => Or.inr (Or.inl ho)), ar⟩
  exact ⟨lower, ⟨C, fan, hs.le, he⟩, C, hm, hs, he⟩

theorem positive {f : BFn 6} (h : ExactNine f) (s : ℕ) (budget : HasCircuitSize 6 f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x := by
  obtain ⟨hl, _, C, hm, hs, he⟩ := h
  exact ⟨C, hm, hs.le.trans (hl s budget), he⟩

set_option maxRecDepth 16384

namespace Row15101

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15101.six :=
  fromWitness witness ThresholdBatch.Row15101.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15101

namespace Row15113

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15113.six :=
  fromWitness witness ThresholdBatch.Row15113.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15113

namespace Row15127

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15127.six :=
  fromWitness witness ThresholdBatch.Row15127.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15127

namespace Row15129

def witness : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15129.six :=
  fromWitness witness ThresholdBatch.Row15129.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15129

namespace Row15139

def witness : Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15139.six :=
  fromWitness witness ThresholdBatch.Row15139.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15139

namespace Row15147

def witness : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15147.six :=
  fromWitness witness ThresholdBatch.Row15147.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15147

namespace Row15151

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [6, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15151.six :=
  fromWitness witness ThresholdBatch.Row15151.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15151

namespace Row15209

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15209.six :=
  fromWitness witness ThresholdBatch.Row15209.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15209

namespace Row15287

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15287.six :=
  fromWitness witness ThresholdBatch.Row15287.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15287

namespace Row15345

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15345.six :=
  fromWitness witness ThresholdBatch.Row15345.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15345

namespace Row15353

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15353.six :=
  fromWitness witness ThresholdBatch.Row15353.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15353

namespace Row15379

def witness : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15379.six :=
  fromWitness witness ThresholdBatch.Row15379.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15379

namespace Row15529

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15529.six :=
  fromWitness witness ThresholdBatch.Row15529.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15529

namespace Row16125

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16125.six :=
  fromWitness witness ThresholdBatch.Row16125.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16125

namespace Row16195

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16195.six :=
  fromWitness witness ThresholdBatch.Row16195.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16195

namespace Row16215

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [6, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16215.six :=
  fromWitness witness ThresholdBatch.Row16215.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16215

namespace Row16257

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16257.six :=
  fromWitness witness ThresholdBatch.Row16257.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16257

namespace Row16267

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16267.six :=
  fromWitness witness ThresholdBatch.Row16267.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16267

namespace Row16361

def witness : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16361.six :=
  fromWitness witness ThresholdBatch.Row16361.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16361

namespace Row16363

def witness : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16363.six :=
  fromWitness witness ThresholdBatch.Row16363.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16363

namespace Row15769

def witness : Circuit := ⟨[⟨.and, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15769.six :=
  fromWitness witness ThresholdBatch.Row15769.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15769

namespace Row15773

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15773.six :=
  fromWitness witness ThresholdBatch.Row15773.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15773

namespace Row16405

def witness : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16405.six :=
  fromWitness witness ThresholdBatch.Row16405.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16405

namespace Row15845

def witness : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15845.six :=
  fromWitness witness ThresholdBatch.Row15845.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15845

namespace Row16537

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16537.six :=
  fromWitness witness ThresholdBatch.Row16537.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16537

namespace Row16545

def witness : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16545.six :=
  fromWitness witness ThresholdBatch.Row16545.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16545

namespace Row16573

def witness : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16573.six :=
  fromWitness witness ThresholdBatch.Row16573.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16573

namespace Row15949

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row15949.six :=
  fromWitness witness ThresholdBatch.Row15949.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row15949

namespace Row16599

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16599.six :=
  fromWitness witness ThresholdBatch.Row16599.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16599

namespace Row16603

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [4, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16603.six :=
  fromWitness witness ThresholdBatch.Row16603.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16603

namespace Row16611

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16611.six :=
  fromWitness witness ThresholdBatch.Row16611.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16611

namespace Row16635

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16635.six :=
  fromWitness witness ThresholdBatch.Row16635.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16635

namespace Row16679

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16679.six :=
  fromWitness witness ThresholdBatch.Row16679.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16679

namespace Row16741

def witness : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16741.six :=
  fromWitness witness ThresholdBatch.Row16741.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16741

namespace Row16743

def witness : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16743.six :=
  fromWitness witness ThresholdBatch.Row16743.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16743

namespace Row16751

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16751.six :=
  fromWitness witness ThresholdBatch.Row16751.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16751

namespace Row16765

def witness : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16765.six :=
  fromWitness witness ThresholdBatch.Row16765.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16765

namespace Row16787

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16787.six :=
  fromWitness witness ThresholdBatch.Row16787.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16787

namespace Row16861

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16861.six :=
  fromWitness witness ThresholdBatch.Row16861.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16861

namespace Row16879

def witness : Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16879.six :=
  fromWitness witness ThresholdBatch.Row16879.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16879

namespace Row16943

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16943.six :=
  fromWitness witness ThresholdBatch.Row16943.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16943

namespace Row16971

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16971.six :=
  fromWitness witness ThresholdBatch.Row16971.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16971

namespace Row16989

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16989.six :=
  fromWitness witness ThresholdBatch.Row16989.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16989

namespace Row16991

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16991.six :=
  fromWitness witness ThresholdBatch.Row16991.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16991

namespace Row16993

def witness : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row16993.six :=
  fromWitness witness ThresholdBatch.Row16993.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row16993

namespace Row17007

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row17007.six :=
  fromWitness witness ThresholdBatch.Row17007.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row17007

namespace Row17045

def witness : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row17045.six :=
  fromWitness witness ThresholdBatch.Row17045.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row17045

namespace Row17069

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row17069.six :=
  fromWitness witness ThresholdBatch.Row17069.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row17069

namespace Row17073

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row17073.six :=
  fromWitness witness ThresholdBatch.Row17073.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row17073

namespace Row17087

def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

theorem exactNine : ExactNine ThresholdBatch.Row17087.six :=
  fromWitness witness ThresholdBatch.Row17087.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end Row17087

end FamilyExact
