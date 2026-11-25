import PositiveTwin

namespace Row16752.Threshold

def score (w : Fin 6 → ℕ) (x : Fin 6 → Bool) :=
  (if x 0 then w 0 else 0) + (if x 1 then w 1 else 0) + (if x 2 then w 2 else 0) +
  (if x 3 then w 3 else 0) + (if x 4 then w 4 else 0) + (if x 5 then w 5 else 0)

def leastWeights : Fin 6 → ℕ := ![8,4,3,3,2,1]
def assignment (r : ℕ) : Fin 6 → Bool := fun i => r.testBit i.val

set_option maxRecDepth 8192 in
theorem weighted : ∀ x, target x = decide (8 ≤ score leastWeights x) := by decide +kernel

set_option maxRecDepth 8192 in
theorem essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool, target (Function.update x i (!x i)) ≠ target x := by
  intro i
  exact ⟨assignment ((![0,12,10,6,6,6] : Fin 6 → ℕ) i), by revert i; decide +kernel⟩

theorem least {w : Fin 6 → ℕ} {q : ℕ} (h : ∀ x, target x = decide (q ≤ score w x)) :
    8 ≤ q ∧ ∀ i, leastWeights i ≤ w i := by
  have h1 : q ≤ w 0 := by
    have e := h (assignment 1)
    rw [show target (assignment 1) = true by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h38 : q ≤ w 1 + w 2 + w 5 := by
    have e := h (assignment 38)
    rw [show target (assignment 38) = true by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h42 : q ≤ w 1 + w 3 + w 5 := by
    have e := h (assignment 42)
    rw [show target (assignment 42) = true by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h28 : q ≤ w 2 + w 3 + w 4 := by
    have e := h (assignment 28)
    rw [show target (assignment 28) = true by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h6 : w 1 + w 2 < q := by
    have e := h (assignment 6)
    rw [show target (assignment 6) = false by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h44 : w 2 + w 3 + w 5 < q := by
    have e := h (assignment 44)
    rw [show target (assignment 44) = false by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  have h50 : w 1 + w 4 + w 5 < q := by
    have e := h (assignment 50)
    rw [show target (assignment 50) = false by decide +kernel] at e
    simpa [score, assignment, Nat.testBit, Nat.shiftRight] using e.symm
  refine ⟨by omega, ?_⟩
  intro i
  fin_cases i
  · change 8 ≤ w 0; omega
  · change 4 ≤ w 1; omega
  · change 3 ≤ w 2; omega
  · change 3 ≤ w 3; omega
  · change 2 ≤ w 4; omega
  · change 1 ≤ w 5; omega

end Row16752.Threshold
#print axioms Row16752.Threshold.least
#print axioms Row16752.Threshold.essential
