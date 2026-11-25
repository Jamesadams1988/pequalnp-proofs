import FilteredOutput
import Upper114

namespace Row9802.Rectangles
open Row4201.RectanglePlane Row4201.StarBound

/-- Keep the plane's original wire labels when deleting point 0 and line 22. -/
def embed (v : Fin 40) : V := if v.val < 21 then ⟨v.val + 1, by omega⟩ else ⟨v.val + 2, by omega⟩
def remaining : Finset E := target.filter fun e => e.1 ≠ 0 ∧ e.2 ≠ 22

set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem literalEdges : ∀ u v : Fin 40,
    (u.val,v.val) ∈ Row9802.Upper114.edges ↔ (embed u,embed v) ∈ remaining := by
  simp only [remaining,target,Finset.mem_filter,Finset.mem_univ,true_and]
  decide +kernel

def matching : Finset E := Finset.univ.image fun i : Fin 20 =>
  (embed ⟨i.val,by omega⟩,embed ⟨20+i.val,by omega⟩)

theorem edgeCount : remaining.card = 95 := by decide +kernel
theorem matchingSize : matching.card = 20 := by decide +kernel
theorem matchingValid : matching ⊆ remaining := by decide +kernel
theorem disjointEnds : ∀ c : V, (matching.filter fun e => e.1=c ∨ e.2=c).card ≤ 1 := by
  decide +kernel

private theorem oldEdge {e : E} (he : e ∈ remaining) : e ∈ target :=
  (Finset.mem_filter.mp he).1

private theorem origins {products bank : Finset (Finset E)} {o : ℕ} (post : Filtered products o bank) :
    ∀ s ∈ bank, ∀ e ∈ s, ∃ r ∈ products, e ∈ r := by
  induction post with
  | init => exact fun s hs e he => ⟨s,hs,he⟩
  | join p ha hb ih =>
    intro s hs e he
    rcases Finset.mem_insert.mp hs with rfl | old
    · exact (Finset.mem_union.mp he).elim (ih _ ha e) (ih _ hb e)
    · exact ih s old e he
  | delete p ha sub ih =>
    intro s hs e he
    rcases Finset.mem_insert.mp hs with rfl | old
    · exact ih _ ha e (sub he)
    · exact ih s old e he

private theorem owns {r : Finset E} {S : Finset V} {c : V} (hr : r = S.image (edge c)) :
    (r ∩ matching).card ≤ 1 := by
  apply le_trans (Finset.card_le_card (t := matching.filter fun e => e.1=c ∨ e.2=c) ?_) (disjointEnds c)
  intro e he
  obtain ⟨er,em⟩ := Finset.mem_inter.mp he
  rw [hr] at er
  obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp er
  refine Finset.mem_filter.mpr ⟨em,?_⟩
  by_cases h : c ≤ d
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (max_eq_left (le_of_not_ge h))

/-- Charge each distinct sound product once, and charge the shared ORs at both
ends. Postprocessing is allowed to remove any edges for free. It can include
intersections of products at any depth. -/
theorem sharpBudget {initial inputBank : Finset (Finset V)} {products outputBank : Finset (Finset E)}
    {i o : ℕ} {s : Finset E}
    (seeds : ∀ A ∈ initial, A.card ≤ 1) (pre : Joins initial i inputBank)
    (middle : ∀ r ∈ products, ∃ A ∈ inputBank, ∃ B ∈ inputBank, r = rectangle A B)
    (valid : ∀ r ∈ products, r ⊆ remaining) (post : Filtered products o outputBank)
    (out : s ∈ outputBank) (covers : remaining ⊆ s) :
    94 ≤ i+o ∧ 20 ≤ products.card ∧ 114 ≤ i+o+products.card := by
  have stars (r) (hr : r ∈ products) : ∃ A ∈ inputBank, ∃ c : V,
      A ⊆ neighbors c ∧ r = A.image (edge c) := by
    obtain ⟨A,ha,B,hb,eq⟩ := middle r hr
    have sound : rectangle A B ⊆ target := fun e he => oldEdge (valid r hr (eq.symm ▸ he))
    rw [eq]
    exact rectangleStar ha hb sound
  obtain ⟨P,sz,inp⟩ := inner neighbors edge thin seeds pre
  have paid (r) (hr : r ∈ products) : almost r P := by
    obtain ⟨A,ha,c,sub,rfl⟩ := stars r hr
    exact inp A ha c sub
  obtain ⟨Q,hQ,final⟩ := deletionBound post paid
  have residual := final s out
  have subset : remaining ⊆ Q ∪ (s \ Q) := by
    intro e he
    by_cases h : e ∈ Q
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨covers he,h⟩)
  have oc := (Finset.card_le_card subset).trans (Finset.card_union_le ..)
  unfold almost at residual
  rw [edgeCount] at oc
  have coverMatch : matching ⊆ products.biUnion (fun r => r ∩ matching) := by
    intro e he
    obtain ⟨r,hr,er⟩ := origins post s out e (covers (matchingValid he))
    exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨er,he⟩⟩
  have count := (Finset.card_le_card coverMatch).trans Finset.card_biUnion_le
  have sum_le : (∑ r ∈ products, (r ∩ matching).card) ≤ ∑ _ ∈ products, 1 := by
    apply Finset.sum_le_sum
    intro r hr
    obtain ⟨A,_,c,_,eq⟩ := stars r hr
    exact owns eq
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at sum_le
  rw [matchingSize] at count
  omega

end Row9802.Rectangles
#print axioms Row9802.Rectangles.sharpBudget
