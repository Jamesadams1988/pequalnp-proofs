import Witnesses

namespace FirstWire17336

/-- The literal proposition of the accepted upstream theorem. -/
abbrev Lower17335 : Prop :=
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size

/-- The exact sizes attained for a prescribed semantic OR on wire 9. -/
def orFirstSizes (j : Fin 9) : Set Nat :=
  {s | ∃ C, Meets C s (fun x => x 5 || x j)}

/-- Every admissible OR-first position has least unrestricted fan-in-two size 16. -/
theorem exactOrFirstOfLower (h : Lower17335) (j : Fin 9) (hj : 5 < j) :
    IsLeast (orFirstSizes j) 16 := by
  constructor
  · have choices : j = 6 ∨ j = 7 ∨ j = 8 := by
      have bound := j.isLt
      change 5 < j.val at hj
      have vals : j.val = 6 ∨ j.val = 7 ∨ j.val = 8 := by omega
      rcases vals with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases choices with rfl | rfl | rfl
    · exact ⟨or5_6, or5_6_spec⟩
    · exact ⟨or5_7, or5_7_spec⟩
    · exact ⟨or5_8, or5_8_spec⟩
  · rintro s ⟨C, hfan, hsize, hwire, hfun⟩
    rw [← hsize]
    exact h C hfan (Or.inr (Or.inr ⟨j, hj, hwire⟩)) hfun

#print axioms exactOrFirstOfLower

end FirstWire17336
