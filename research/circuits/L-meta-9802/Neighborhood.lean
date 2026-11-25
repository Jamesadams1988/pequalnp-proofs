import Mathlib.Data.Finset.Union

namespace Row9802.Neighborhood

variable {P L : Type*} [DecidableEq L]

/-- `S` on the point side and the complement of its neighborhood on the line side is independent. -/
theorem independent (N : P → Finset L) (S : Finset P) :
    ¬ ∃ p l, l ∈ N p ∧ p ∈ S ∧ l ∉ S.biUnion N := by
  rintro ⟨p,l,edge,hp,hl⟩
  exact hl (Finset.mem_biUnion.mpr ⟨p,hp,edge⟩)

/-- If the neighborhoods differ, the union of the two independent assignments contains a listed edge. -/
theorem separates (N : P → Finset L) {S T : Finset P} (ne : S.biUnion N ≠ T.biUnion N) :
    ∃ p l, l ∈ N p ∧ (p ∈ S ∨ p ∈ T) ∧ (l ∉ S.biUnion N ∨ l ∉ T.biUnion N) := by
  by_contra missing
  apply ne
  ext l
  constructor
  · intro h
    by_contra no
    obtain ⟨p,hp,edge⟩ := Finset.mem_biUnion.mp h
    exact missing ⟨p,l,edge,.inl hp,.inr no⟩
  · intro h
    by_contra no
    obtain ⟨p,hp,edge⟩ := Finset.mem_biUnion.mp h
    exact missing ⟨p,l,edge,.inr hp,.inl no⟩

end Row9802.Neighborhood
#print axioms Row9802.Neighborhood.separates
