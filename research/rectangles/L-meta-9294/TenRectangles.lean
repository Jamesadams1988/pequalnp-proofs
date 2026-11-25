import PEqualNP.Defs

/- A ten-rectangle witness for the one entries of the L-meta-9294 matrix.
   James Adams (Jamesadams1988). -/
namespace RectangleCover9294

def cover : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [({0, 2, 4, 7}, {1, 5}),
    ({0, 1, 5, 7}, {2, 4}),
    ({0, 1, 2, 6, 8, 9}, {3}),
    ({0, 3, 4, 5, 8, 9}, {6}),
    ({1, 2, 3, 4, 5, 6}, {0}),
    ({1, 2, 4, 5, 8, 9}, {7}),
    ({1, 3, 7, 9}, {2, 8}),
    ({2, 3, 7, 8}, {1, 9}),
    ({4, 6, 7, 9}, {5, 8}),
    ({5, 6, 7, 8}, {4, 9})]

theorem ten_suffice :
    ∃ L : List (Finset (Fin 10) × Finset (Fin 10)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([126, 413, 683, 839, 483, 725, 825, 822, 730, 492] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 10) (j : Fin 10), (([126, 413, 683, 839, 483, 725, 825, 822, 730, 492] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨cover, by decide, ?_, ?_⟩
  · intro r hr
    simp only [cover, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
  · intro i j hij
    have h : ∀ a b : Fin 10,
        (([126, 413, 683, 839, 483, 725, 825, 822, 730, 492] : List ℕ).getD a.val 0).testBit b.val = true →
        cover.any (fun r => decide (a ∈ r.1 ∧ b ∈ r.2)) = true := by decide
    obtain ⟨r, hr, hmem⟩ := List.any_eq_true.mp (h i j hij)
    exact ⟨r, hr, of_decide_eq_true hmem⟩

end RectangleCover9294
