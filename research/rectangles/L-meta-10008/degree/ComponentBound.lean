import PEqualNP.Defs

namespace RectangleDegree

open Finset

/-- Distinct two-coordinate row signatures in one component. -/
theorem pairCapacity {P V : Type*} [DecidableEq P] [DecidableEq V]
    (rows : Finset P) (coordinates : Finset V) (code : P → Finset V)
    (size : ∀ p ∈ rows, (code p).card = 2)
    (inside : ∀ p ∈ rows, code p ⊆ coordinates)
    (inj : Set.InjOn code (rows : Set P)) :
    rows.card ≤ coordinates.card.choose 2 := by
  have sub : rows.image code ⊆ coordinates.powersetCard 2 := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_powersetCard.mpr ⟨inside p hp,size p hp⟩
  simpa [Finset.card_image_of_injOn inj] using Finset.card_le_card sub

/-- In a connected group the point count is at most six. A one-point
private component is also allowed. Keep the single extra unit for size six. -/
theorem component (e v : Nat) (bound : e ≤ 6)
    (codes : e ≤ 1 ∧ 0 < v ∨ e ≤ v.choose 2) :
    4 * e ≤ 5 * v + (if e = 6 then 4 else 0) := by
  by_cases big : 5 ≤ v
  · split <;> omega
  · have small : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by omega
    rcases small with h|h|h|h|h <;> subst v <;>
      norm_num [Nat.choose] at codes ⊢ <;> split <;> omega

/-- The geometric component decomposition has at most one full line. This
lemma turns its arithmetic premises into the cover-size inequality. -/
theorem aggregate {G : Type*} [DecidableEq G] (parts : Finset G)
    (points rectangles : G → Nat)
    (cap : ∀ g ∈ parts, points g ≤ 6)
    (codes : ∀ g ∈ parts, points g ≤ 1 ∧ 0 < rectangles g ∨
      points g ≤ (rectangles g).choose 2)
    (uniqueFull : (parts.filter fun g => points g = 6).card ≤ 1) :
    4 * (∑ g ∈ parts, points g) ≤ 5 * (∑ g ∈ parts, rectangles g) + 4 := by
  have h := Finset.sum_le_sum (s:=parts)
    (fun g hg => component (points g) (rectangles g) (cap g hg) (codes g hg))
  have extra : (∑ g ∈ parts, if points g = 6 then 4 else 0) ≤ 4 := by
    rw [← Finset.sum_filter]
    simpa using Nat.mul_le_mul_right 4 uniqueFull
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  omega

theorem atMostTwentyTwo (low m : Nat) (hm : m ≤ 17)
    (h : 4 * low ≤ 5 * m + 4) : low ≤ 22 := by omega

theorem atLeastTwentyFour (m : Nat) (h : 4 * 31 ≤ 5 * m + 4) : 24 ≤ m := by omega

end RectangleDegree
#print axioms RectangleDegree.pairCapacity
#print axioms RectangleDegree.aggregate
