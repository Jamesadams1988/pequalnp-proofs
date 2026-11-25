import PEqualNP.Defs

namespace NonincidenceCover

abbrev Vertex := Fin 31

def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]

def incident (p l : Vertex) : Bool := (rows.getD p.val 0).testBit l.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem unique_join : ∀ p q : Vertex, p ≠ q → ∃! l : Vertex, incident p l ∧ incident q l := by
  unfold ExistsUnique
  decide +kernel

set_option maxRecDepth 10000 in
theorem separate : ∀ p q : Vertex, p ≠ q → ∃ l : Vertex, incident p l ∧ ¬ incident q l := by
  decide +kernel

abbrev Box := Finset Vertex × Finset Vertex

def Plain (b : Box) := ∀ x ∈ b.1, ∀ l ∈ b.2, ¬ incident x l

def RowCovered (R : List Box) (p : Vertex) :=
  ∀ l : Vertex, ¬ incident p l → ∃ b ∈ R, p ∈ b.1 ∧ l ∈ b.2

theorem unique_support_singleton (R : List Box) (p : Vertex) (a : Box)
    (sound : ∀ b ∈ R, Plain b) (covers : RowCovered R p) (has : p ∈ a.1)
    (only : ∀ b ∈ R, p ∈ b.1 → b = a) : a.1 = {p} := by
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hne
    obtain ⟨l, hxl, hpl⟩ := separate x p hne
    obtain ⟨b,hb,hp,hl⟩ := covers l hpl
    cases only b hb hp
    exact sound _ hb _ hx _ hl hxl
  · rintro rfl
    exact has

private theorem forced_line (a b : Finset Vertex) (p x l : Vertex)
    (forces : ∀ z ∈ a, ∀ y ∈ b, ∀ l, incident z l → incident y l → incident p l)
    (hx : x ∈ a) (hne : p ≠ x) (hlp : incident p l) (hlx : incident x l) :
    ∀ y ∈ b, incident y l := by
  intro y hy
  by_cases eq : x = y
  · simpa [← eq] using hlx
  obtain ⟨j, ⟨hjx,hjy⟩, _⟩ := unique_join x y eq
  have hjp := forces x hx y hy j hjx hjy
  obtain ⟨k, _, uniq⟩ := unique_join p x hne
  have hjl : j = l := (uniq _ ⟨hjp,hjx⟩).trans (uniq _ ⟨hlp,hlx⟩).symm
  simpa [hjl] using hjy

/-- Two nonsingleton row supports covering a row intersect only there and share a carrier line. -/
theorem two_supports (R : List Box) (p : Vertex) (a b : Box)
    (sound : ∀ t ∈ R, Plain t) (covers : RowCovered R p)
    (only : ∀ t ∈ R, p ∈ t.1 → t = a ∨ t = b)
    (hpa : p ∈ a.1) (hpb : p ∈ b.1)
    (ha : ∃ x ∈ a.1, p ≠ x) (hb : ∃ y ∈ b.1, p ≠ y) :
    a.1 ∩ b.1 = {p} ∧ ∃ l : Vertex, ∀ z ∈ a.1 ∪ b.1, incident z l := by
  have forces : ∀ x ∈ a.1, ∀ y ∈ b.1, ∀ l, incident x l → incident y l → incident p l := by
    intro x hx y hy l hxl hyl
    by_contra hn
    obtain ⟨t,ht,hpt,hlt⟩ := covers l hn
    rcases only t ht hpt with rfl | rfl
    · exact sound _ ht _ hx _ hlt hxl
    · exact sound _ ht _ hy _ hlt hyl
  constructor
  · ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    constructor
    · rintro ⟨hza,hzb⟩
      by_contra hne
      obtain ⟨l,hzl,hn⟩ := separate z p hne
      exact hn (forces z hza z hzb l hzl hzl)
    · rintro rfl
      exact ⟨hpa,hpb⟩
  · obtain ⟨x,hx,hnx⟩ := ha
    obtain ⟨y,hy,hny⟩ := hb
    obtain ⟨l,⟨hlp,hlx⟩,_⟩ := unique_join p x hnx
    have right := forced_line a.1 b.1 p x l forces hx hnx hlp hlx
    have left := forced_line b.1 a.1 p y l
      (fun v hv w hw j hvj hwj => forces w hw v hv j hwj hvj) hy hny hlp (right y hy)
    exact ⟨l,fun z hz => (Finset.mem_union.mp hz).elim (left z) (right z)⟩

/-- Rectangle indices permit repeated rectangle values in the list. -/
def supportCode (R : List Box) (p : Vertex) : Finset (Fin R.length) :=
  Finset.univ.filter (fun t => p ∈ (R.get t).1)

/-- Each pair of distinct rows is separated in the indicated direction by a rectangle coordinate. -/
theorem support_separates (R : List Box) (p q : Vertex)
    (sound : ∀ t ∈ R, Plain t) (covers : RowCovered R p) (hne : p ≠ q) :
    ∃ i ∈ supportCode R p, i ∉ supportCode R q := by
  obtain ⟨l,hql,hnp⟩ := separate q p hne.symm
  obtain ⟨b,hb,hp,hl⟩ := covers l hnp
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
  refine ⟨i, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hi.symm ▸ hp⟩
  · intro h
    have hiq : q ∈ (R.get i).1 := (Finset.mem_filter.mp h).2
    have hq : q ∈ b.1 := hi ▸ hiq
    exact sound b hb q hq l hl hql

theorem supportCode_injective (R : List Box) (S : Set Vertex)
    (sound : ∀ t ∈ R, Plain t) (covers : ∀ p ∈ S, RowCovered R p) :
    Set.InjOn (supportCode R) S := by
  intro p hp q _ eq
  by_contra ne
  obtain ⟨i,hip,hiq⟩ := support_separates R p q sound (covers p hp) ne
  exact hiq (eq ▸ hip)

theorem carrier_unique (S : Finset Vertex) (p x l j : Vertex) (hp : p ∈ S)
    (hx : x ∈ S) (hne : p ≠ x) (hl : ∀ z ∈ S, incident z l)
    (hj : ∀ z ∈ S, incident z j) : l = j := by
  obtain ⟨_, _, uniq⟩ := unique_join p x hne
  exact (uniq _ ⟨hl p hp,hl x hx⟩).trans (uniq _ ⟨hj p hp,hj x hx⟩).symm

def foolingSix : List (Vertex × Vertex) :=
  [(8,25),(13,28),(16,12),(21,11),(18,20),(5,17)]

theorem foolingSix_checked : foolingSix.length = 6 ∧
    (∀ z ∈ foolingSix, ¬ incident z.1 z.2) ∧
    foolingSix.Pairwise (fun u v => incident u.1 v.2 ∨ incident v.1 u.2) := by
  decide +kernel

#print axioms NonincidenceCover.supportCode_injective
#print axioms NonincidenceCover.carrier_unique
#print axioms NonincidenceCover.foolingSix_checked
#print axioms NonincidenceCover.two_supports
#print axioms NonincidenceCover.unique_support_singleton

end NonincidenceCover
