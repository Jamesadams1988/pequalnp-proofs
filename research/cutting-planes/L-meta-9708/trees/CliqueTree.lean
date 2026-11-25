import Mathlib

namespace CliqueCapacityTree
open Finset
variable {V : Type*} [DecidableEq V]

/-- Blocks meet in at most one point when their sets of pairs are disjoint. -/
def Linear (blocks : Finset (Finset V)) : Prop :=
  ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → (a ∩ b).card ≤ 1

def Joins (points : Finset V) (blocks : Finset (Finset V)) : Prop :=
  ∀ p ∈ points, ∀ q ∈ points, p ≠ q → ∃ b ∈ blocks, p ∈ b ∧ q ∈ b

/-- In the absence of a block missing at most one point, four points carry
    at most two points in any block. -/
theorem quadrangle (points : Finset V) (blocks : Finset (Finset V))
    (size : 4 ≤ points.card) (inside : ∀ b ∈ blocks, b ⊆ points)
    (lin : Linear blocks) (joins : Joins points blocks)
    (outside : ∀ b ∈ blocks, 2 ≤ (points \ b).card) :
    ∃ q ⊆ points, q.card = 4 ∧ ∀ b ∈ blocks, (q ∩ b).card ≤ 2 := by
  classical
  by_cases small : ∀ b ∈ blocks, b.card ≤ 2
  · obtain ⟨q, hq, hsize⟩ := exists_subset_card_eq size
    exact ⟨q, hq, hsize, fun b hb => (card_le_card inter_subset_right).trans (small b hb)⟩
  push Not at small
  obtain ⟨a, ha, big⟩ := small
  obtain ⟨y, hy, cy⟩ := exists_subset_card_eq (outside a ha)
  obtain ⟨p, r, hpr, hyr⟩ := card_eq_two.mp cy
  have ypts : y ⊆ points := fun v hv => (mem_sdiff.mp (hy hv)).1
  have hpy : p ∈ y := by simp [hyr]
  have hry : r ∈ y := by simp [hyr]
  obtain ⟨d, hd, hpd, hrd⟩ := joins p (ypts hpy) r (ypts hry) hpr
  have hda : d ≠ a := fun e => (mem_sdiff.mp (hy hpy)).2 (e ▸ hpd)
  have yd : y ⊆ d := by
    intro v hv
    rw [hyr, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hpd
    · exact hrd
  have ad := lin d hd a ha hda
  have hroom : 2 ≤ (a \ d).card := by rw [card_sdiff]; omega
  obtain ⟨x, hx, cx⟩ := exists_subset_card_eq hroom
  have xa : x ⊆ a := fun v hv => (mem_sdiff.mp (hx hv)).1
  have ds : Disjoint x y := disjoint_left.mpr fun v hv hv' => (mem_sdiff.mp (hx hv)).2 (yd hv')
  refine ⟨x ∪ y, union_subset (xa.trans (inside a ha)) ypts, ?_, ?_⟩
  · rw [card_union_of_disjoint ds, cx, cy]
  intro b hb
  by_cases e : b = a
  · subst b
    have sub : (x ∪ y) ∩ a ⊆ x := by
      intro v hv
      rcases mem_union.mp (mem_inter.mp hv).1 with h | h
      · exact h
      · exact False.elim ((mem_sdiff.mp (hy h)).2 (mem_inter.mp hv).2)
    exact (card_le_card sub).trans cx.le
  by_cases f : b = d
  · subst b
    have sub : (x ∪ y) ∩ d ⊆ y := by
      intro v hv
      rcases mem_union.mp (mem_inter.mp hv).1 with h | h
      · exact False.elim ((mem_sdiff.mp (hx h)).2 (mem_inter.mp hv).2)
      · exact h
    exact (card_le_card sub).trans cy.le
  have bx : (x ∩ b).card ≤ 1 := (card_le_card (inter_subset_inter xa (Subset.refl b))).trans (lin a ha b hb (Ne.symm e))
  have by' : (y ∩ b).card ≤ 1 := (card_le_card (inter_subset_inter yd (Subset.refl b))).trans (lin d hd b hb (Ne.symm f))
  rw [union_inter_distrib_right]
  exact (card_union_le _ _).trans (by omega)

/-- A successful rounded nonnegative weighted sum of block capacities to a
    single clique capacity forces a block missing at most one vertex. -/
theorem nearPencil (points : Finset V) (blocks : Finset (Finset V))
    (size : 4 ≤ points.card) (inside : ∀ b ∈ blocks, b ⊆ points)
    (lin : Linear blocks) (joins : Joins points blocks)
    (w : Finset V → ℕ) (d : ℕ)
    (uniform : ∀ v ∈ points, (∑ b ∈ blocks, if v ∈ b then w b else 0) = d)
    (rounds : (∑ b ∈ blocks, w b) < 2 * d) :
    ∃ b ∈ blocks, (points \ b).card ≤ 1 := by
  classical
  by_contra! missing
  obtain ⟨q, hq, cq, cap⟩ := quadrangle points blocks size inside lin joins missing
  have e : ∑ v ∈ q, ∑ b ∈ blocks, (if v ∈ b then w b else 0) = 4*d := by
    simp [Finset.sum_congr rfl (fun v hv => uniform v (hq hv)), cq]
  rw [Finset.sum_comm] at e
  have bound : ∀ b ∈ blocks, (∑ v ∈ q, if v ∈ b then w b else 0) ≤ 2 * w b := by
    intro b hb
    rw [← Finset.sum_filter]
    have filt : q.filter (fun v => v ∈ b) = q ∩ b := by ext; simp
    rw [filt, Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (cap b hb)
  have h := Finset.sum_le_sum bound
  rw [← Finset.mul_sum, e] at h
  omega

/-- Equal coefficients in a near-pencil force every star edge to have
    the same multiplicity and the central block to have multiplicity m−1
    times as large, where m is the size of the central block. -/
theorem starWeights {m : ℕ} (w : Fin m → ℕ) (c d : ℕ)
    (atLeaf : ∀ i, c + w i = d) (atCenter : (∑ i, w i) = d) (i : Fin m) :
    (∀ j, w j = w i) ∧ c = (m-1)*w i := by
  have same : ∀ j, w j = w i := by
    intro j
    have a := atLeaf i
    have b := atLeaf j
    omega
  refine ⟨same, ?_⟩
  have e : m * w i = d := by
    convert atCenter using 1
    calc m * w i = ∑ _ : Fin m, w i := by simp
         _ = ∑ j : Fin m, w j := Finset.sum_congr rfl (fun j _ => (same j).symm)
  have mpos := i.isLt
  have ht : m = (m-1)+1 := by omega
  conv_lhs at e => lhs; rw [ht]
  rw [Nat.add_mul, Nat.one_mul] at e
  have a := atLeaf i
  omega

end CliqueCapacityTree
#print axioms CliqueCapacityTree.nearPencil
#print axioms CliqueCapacityTree.starWeights
