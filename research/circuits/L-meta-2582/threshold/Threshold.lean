import PEqualNP.Outside.L_meta_2393
import ReadMonotone

namespace IncidenceReadTwo.Threshold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

/-- The part of L-meta-2582 at or above the exact line-star gate budget.
    It only uses the column cardinality and positivity of the number of columns. -/
theorem aboveStar (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (positive : 0 < N)
    (degree : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q+1)
    (budget : N*(q+2) ≤ C.size+1) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 2 := by
  obtain ⟨D,ao,correct,readOne,size⟩ := PEqualNP.Outside.L_meta_2393.Own.upper q N I positive degree
  exact ⟨D,ao,correct,by omega,Monotonicity.isReadK_mono (by decide : 1 ≤ 2) D readOne⟩

/-- It suffices to replace strictly sub-star-budget circuits which actually
    fail the joint read-two test. This version has the same quantifiers and
    conclusion as the desk statement when the displayed subproblem is supplied. -/
theorem removeLargeAndAlreadyRead (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (_hq : 2 ≤ q) (hN : N = q^2+q+1)
    (degree : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q+1)
    (_unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C)
    (correct : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (small : C.size+1 < N*(q+2) → ¬ IsReadK (N+N) C 2 →
      ∃ D : Circuit, IsAO2 (N+N) D ∧
        (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK (N+N) D 2) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 2 := by
  by_cases read : IsReadK (N+N) C 2
  · exact ⟨C,ao,correct,le_rfl,read⟩
  by_cases cutoff : N*(q+2) ≤ C.size+1
  · exact aboveStar q N I C (by omega) degree cutoff
  · exact small (by omega) read

end IncidenceReadTwo.Threshold
#print axioms IncidenceReadTwo.Threshold.aboveStar
#print axioms IncidenceReadTwo.Threshold.removeLargeAndAlreadyRead
