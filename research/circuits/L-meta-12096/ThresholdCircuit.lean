import PEqualNP.Defs

/-!
A monotone circuit for the six-input table L-meta-12096.
The lower three inputs enter only through their three order statistics.
The upper two enter only through their disjunction and conjunction.
-/

namespace Row12096.ThresholdCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269866496 * 2^32 + 4261472256)
    (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)

def combine (one two three middle either both : Bool) : Bool :=
  (middle && (two || (one && either))) || (three && both)

def features (x : Fin 6 → Bool) : Fin 6 → Bool :=
  ![x 0 || x 1 || x 2, (x 0 && x 1) || ((x 0 || x 1) && x 2),
    x 0 && x 1 && x 2, x 3, x 4 || x 5, x 4 && x 5]

set_option maxRecDepth 8192 in
theorem factorization : ∀ x, target x = combine (features x 0) (features x 1)
    (features x 2) (features x 3) (features x 4) (features x 5) := by
  decide +kernel

/-- The same table is a weighted threshold with input weights 2,2,2,5,1,1. -/
theorem weightedThreshold : ∀ x, target x = decide
    (8 ≤ 2 * ((x 0).toNat + (x 1).toNat + (x 2).toNat) +
         5 * (x 3).toNat + (x 4).toNat + (x 5).toNat) := by
  decide +kernel

/-- Wires 6–11 compute the three order statistics of inputs 0–2.
Wires 12 and 13 sort inputs 4 and 5. Wires 14–18 implement `combine`. -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩,
    ⟨.and, [6, 2]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [7, 2]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [8, 12]⟩,
    ⟨.or, [10, 14]⟩, ⟨.and, [3, 15]⟩, ⟨.and, [11, 13]⟩,
    ⟨.or, [16, 17]⟩], 18⟩

set_option maxRecDepth 8192 in
theorem upper : Monotone2 witness ∧ witness.size = 13 ∧
    ∀ x, witness.eval (List.ofFn x) = target x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [Monotone2, witness]
  · decide +kernel

end Row12096.ThresholdCircuit

#print axioms Row12096.ThresholdCircuit.factorization
#print axioms Row12096.ThresholdCircuit.weightedThreshold
#print axioms Row12096.ThresholdCircuit.upper
