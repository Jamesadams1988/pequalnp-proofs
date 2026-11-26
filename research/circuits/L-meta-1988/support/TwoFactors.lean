import Mathlib

namespace ProjectivePlaneTwoFactors

abbrev Vertex := Fin 26
abbrev Factor := Finset Vertex → Bool

/-- The first thirteen inputs select points, the last thirteen select lines. -/
def adjacent (v w : Vertex) : Bool :=
  (decide (v.val < 13) != decide (w.val < 13)) &&
  [0, 1, 3, 9].contains ((v.val + w.val) % 13)

def neighbors (v : Vertex) : Finset Vertex := Finset.univ.filter (fun w => adjacent v w)

set_option maxRecDepth 10000 in
theorem degree_four : ∀ v : Vertex, (neighbors v).card = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
theorem common_neighbor_bound :
    ∀ v w : Vertex, v ≠ w → (neighbors v ∩ neighbors w).card ≤ 1 := by decide

def singletons (f : Factor) : Finset Vertex :=
  Finset.univ.filter (fun v => f {v})

def upward (f : Factor) : Prop :=
  ∀ ⦃s t : Finset Vertex⦄, s ⊆ t → f s = true → f t = true

/-- It suffices to evaluate the final AND on at most two selected coordinates. -/
def correctOnPairs (a b : Factor) : Prop :=
  ∀ v w : Vertex, (a {v,w} && b {v,w}) = adjacent v w

theorem singleton_rectangle {a b : Factor} (ha : upward a) (hb : upward b)
    (h : correctOnPairs a b) (v w : Vertex)
    (hv : v ∈ singletons a) (hw : w ∈ singletons b) : w ∈ neighbors v := by
  have hva : a {v} = true := (Finset.mem_filter.mp hv).2
  have hwb : b {w} = true := (Finset.mem_filter.mp hw).2
  have ha' := ha (show {v} ⊆ ({v,w} : Finset Vertex) by simp) hva
  have hb' := hb (show {w} ⊆ ({v,w} : Finset Vertex) by simp) hwb
  have hij := h v w
  rw [ha', hb'] at hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij.symm⟩

theorem small_singleton_factor {a b : Factor} (ha : upward a) (hb : upward b)
    (h : correctOnPairs a b) : (singletons a).card ≤ 1 ∨ (singletons b).card ≤ 1 := by
  by_cases small : (singletons a).card ≤ 1
  · exact Or.inl small
  · obtain ⟨v, hv, w, hw, distinct⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
    have contains : singletons b ⊆ neighbors v ∩ neighbors w := by
      intro u hu
      exact Finset.mem_inter.mpr ⟨singleton_rectangle ha hb h v u hv hu,
        singleton_rectangle ha hb h w u hw hu⟩
    exact Or.inr ((Finset.card_le_card contains).trans (common_neighbor_bound _ _ distinct))

def changesAt (f : Factor) (v : Vertex) : Finset Vertex :=
  (neighbors v).filter (fun w => f {w} = false ∧ f {v,w} = true)

theorem three_changes {f : Factor} (small : (singletons f).card ≤ 1)
    (edges : ∀ v w : Vertex, w ∈ neighbors v → f {v,w} = true)
    (v : Vertex) : 3 ≤ (changesAt f v).card := by
  have eq_sets : changesAt f v = neighbors v \ singletons f := by
    ext w
    simp only [changesAt, Finset.mem_filter, Finset.mem_sdiff, singletons, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨mem, neg, _⟩
      exact ⟨mem, Bool.eq_false_iff.mp neg⟩
    · rintro ⟨mem, neg⟩
      exact ⟨mem, Bool.eq_false_iff.mpr neg, edges _ _ mem⟩
  rw [eq_sets]
  have cover := Finset.card_sdiff_add_card_inter (neighbors v) (singletons f)
  have overlap : (neighbors v ∩ singletons f).card ≤ (singletons f).card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [degree_four] at cover
  omega

/-- One fixed factor is essential in every coordinate, with at least three
different incident one-to-two-vertex witnesses for *each* coordinate. -/
theorem one_factor_sensitive {a b : Factor} (ha : upward a) (hb : upward b)
    (h : correctOnPairs a b) :
    ((singletons a).card ≤ 1 ∧ ∀ v, 3 ≤ (changesAt a v).card) ∨
    ((singletons b).card ≤ 1 ∧ ∀ v, 3 ≤ (changesAt b v).card) := by
  have edges (v w : Vertex) (mem : w ∈ neighbors v) :
      a {v,w} = true ∧ b {v,w} = true := by
    apply (Bool.and_eq_true _ _).mp
    exact (h v w).trans (Finset.mem_filter.mp mem).2
  rcases small_singleton_factor ha hb h with small | small
  · exact Or.inl ⟨small, three_changes small (fun v w mem => (edges v w mem).1)⟩
  · exact Or.inr ⟨small, three_changes small (fun v w mem => (edges v w mem).2)⟩

#print axioms one_factor_sensitive

end ProjectivePlaneTwoFactors
