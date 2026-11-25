import RectangleTruth

namespace Row4201.RectanglePlane
open Row4201.StarBound

/-- A binary OR adds the union of two supports. A deletion may adjoin any
subset of an earlier support, for free; in particular the AND of any number of
earlier signals can be adjoined by taking their intersection. -/
inductive Filtered (start : Finset (Finset E)) : ℕ → Finset (Finset E) → Prop
  | init : Filtered start 0 start
  | join {k bank a b} : Filtered start k bank → a ∈ bank → b ∈ bank →
      Filtered start (k+1) (insert (a ∪ b) bank)
  | delete {k bank a s} : Filtered start k bank → a ∈ bank → s ⊆ a →
      Filtered start k (insert s bank)

theorem Filtered.meet {start bank a b k} (p : Filtered start k bank) (ha : a ∈ bank) :
    Filtered start k (insert (a ∩ b) bank) := .delete p ha Finset.inter_subset_left

theorem deletionBound {start bank : Finset (Finset E)} {k : ℕ} {P : Finset E}
    (p : Filtered start k bank) (seed : ∀ R ∈ start, almost R P) :
    ∃ Q : Finset E, Q.card ≤ P.card+k ∧ ∀ R ∈ bank, almost R Q := by
  induction p with
  | init => exact ⟨P,by omega,seed⟩
  | join p ha hb ih =>
    obtain ⟨old,limit,ok⟩ := ih
    obtain ⟨fresh,inc,sz,combined⟩ := repair (ok _ ha) (ok _ hb)
    refine ⟨fresh,by omega,?_⟩
    intro R hr
    rcases Finset.mem_insert.mp hr with rfl | prior
    · exact combined
    · apply le_trans (Finset.card_le_card ?_) (ok R prior)
      intro e he
      obtain ⟨er,ne⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨er,fun h => ne (inc h)⟩
  | delete p ha sub ih =>
    obtain ⟨P,sz,ok⟩ := ih
    refine ⟨P,sz,?_⟩
    intro R hr
    rcases Finset.mem_insert.mp hr with rfl | prior
    · apply le_trans (Finset.card_le_card ?_) (ok _ ha)
      intro e he
      obtain ⟨er,ne⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨sub er,ne⟩
    · exact ok R prior

/-- Even unrestricted unpaid deletions after sound rectangles preserve the OR
lower bound. This covers arbitrarily many outer AND layers on the incidence
pair assignments. Every target edge must still be accepted at the output. -/
theorem soundRectanglesWithDeletions {initial inputBank : Finset (Finset V)}
    {products outputBank : Finset (Finset E)} {i o : ℕ} {s : Finset E}
    (seeds : ∀ S ∈ initial, S.card ≤ 1) (pre : Joins initial i inputBank)
    (middle : ∀ R ∈ products, ∃ A ∈ inputBank, ∃ B ∈ inputBank, R = rectangle A B)
    (valid : ∀ R ∈ products, R ⊆ target) (post : Filtered products o outputBank)
    (output : s ∈ outputBank) (covers : target ⊆ s) : 104 ≤ i+o := by
  obtain ⟨P,sz,ok⟩ := inner neighbors edge thin seeds pre
  have paid (R) (hr : R ∈ products) : almost R P := by
    obtain ⟨A,ha,B,hb,rfl⟩ := middle R hr
    obtain ⟨S,hs,c,sub,eq⟩ := rectangleStar ha hb (valid _ hr)
    rw [eq]
    exact ok S hs c sub
  obtain ⟨Q,hQ,done⟩ := deletionBound post paid
  have residual := done s output
  have sub : target ⊆ Q ∪ (s \ Q) := by
    intro e he
    by_cases eq : e ∈ Q
    · exact Finset.mem_union_left _ eq
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨covers he,eq⟩)
  have h := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  unfold almost at residual
  rw [total] at h
  omega

end Row4201.RectanglePlane
#print axioms Row4201.RectanglePlane.soundRectanglesWithDeletions
