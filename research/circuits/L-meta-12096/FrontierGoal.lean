import Symmetry
import ThresholdCircuit

/-! The public row follows from the signed first-gate exclusions or their eighteen symmetry representatives. The
thirteen-gate witness is supplied by the checked circuit construction. -/
namespace Row12096Goal

open Row12096Signed
open Row12096.ThresholdCircuit

theorem ofFirstGateExclusions
    (reject : ∀ p ∈ heads, optimized 10 p.1 p.2 = false) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  obtain ⟨hm, hs, he⟩ := upper
  exact replacement reject ⟨witness, hm, hs.le, he⟩

theorem ofRepresentativeExclusions
    (reject : ∀ p ∈ Symmetry.representatives, optimized 10 p.1 p.2 = false) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  obtain ⟨hm, hs, he⟩ := upper
  exact Symmetry.replacement18 reject ⟨witness, hm, hs.le, he⟩

end Row12096Goal
#print axioms Row12096Goal.ofFirstGateExclusions
#print axioms Row12096Goal.ofRepresentativeExclusions
