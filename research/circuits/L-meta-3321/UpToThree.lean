import Three

namespace SmallIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ForestIncidence

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rectN {N : ℕ} (B : Fin N → Fin N → Bool) := ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬(B p l = true ∧ B p l' = true ∧ B p' l = true ∧ B p' l' = true)

def cutsN {N : ℕ} (B : Fin N → Fin N → Bool) := Separated (fun p l => B p l = true)

instance {N : ℕ} (B : Fin N → Fin N → Bool) : Decidable (rectN B) := by unfold rectN; infer_instance
instance {N : ℕ} (B : Fin N → Fin N → Bool) : Decidable (cutsN B) := by unfold cutsN Separated; infer_instance

private theorem cases0 : ∀ B : Fin 0 → Fin 0 → Bool, rectN B → cutsN B := by decide +kernel
private theorem cases1 : ∀ B : Fin 1 → Fin 1 → Bool, rectN B → cutsN B := by decide +kernel
private theorem cases2 : ∀ B : Fin 2 → Fin 2 → Bool, rectN B → cutsN B := by decide +kernel

private theorem fewer_than_three :
    ∀ n : Fin 3, ∀ B : Fin n → Fin n → Bool,
    (∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬(B p l = true ∧ B p l' = true ∧ B p' l = true ∧ B p' l' = true)) →
    Separated (fun p l => B p l = true) := by
  intro n
  fin_cases n
  · exact cases0
  · exact cases1
  · exact cases2

theorem normalization_le_three (N : ℕ) (small : N ≤ 3) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (free : ∀ p p' l l', p ≠ p' → l ≠ l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (mono : Monotone2 C) (correct : ∀ z, circuitFun (N+N) C z = true ↔ incidence I z) :
    ∃ D, Normal I C D := by
  rcases lt_or_eq_of_le small with smaller | rfl
  · let B (p l : Fin N) := decide (I p l)
    have cuts := fewer_than_three ⟨N,smaller⟩ B (by simpa only [B,decide_eq_true_eq] using free)
    apply forest_normalization I C _ mono correct
    apply forest_of_separated
    simpa only [Separated,B,decide_eq_true_eq] using cuts
  · exact three_normalization I C free mono correct

#print axioms normalization_le_three
end SmallIncidence
