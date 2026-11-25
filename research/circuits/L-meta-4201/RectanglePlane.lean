import StarBound

namespace Row4201.RectanglePlane
open Row4201.StarBound
abbrev V := Fin 42
abbrev E := V × V

/-- Exactly the point/line predicate in L-meta-4201, with the original variable indices. -/
def oriented (a b : V) : Bool := decide (a.val < 21 ∧ 21 ≤ b.val ∧
    (b.val + 21 - a.val) % 21 ∈ [0,5,7,17,20])
def target : Finset E := Finset.univ.filter (fun p => oriented p.1 p.2)
def edge (a b : V) : E := (min a b, max a b)
theorem edgeSymm (a b : V) : edge a b = edge b a := by simp [edge,min_comm,max_comm]

def neighbors : V → Finset V := ![
  {21,26,28,38,41},
  {21,22,27,29,39},
  {22,23,28,30,40},
  {23,24,29,31,41},
  {21,24,25,30,32},
  {22,25,26,31,33},
  {23,26,27,32,34},
  {24,27,28,33,35},
  {25,28,29,34,36},
  {26,29,30,35,37},
  {27,30,31,36,38},
  {28,31,32,37,39},
  {29,32,33,38,40},
  {30,33,34,39,41},
  {21,31,34,35,40},
  {22,32,35,36,41},
  {21,23,33,36,37},
  {22,24,34,37,38},
  {23,25,35,38,39},
  {24,26,36,39,40},
  {25,27,37,40,41},
  {0,1,4,14,16},
  {1,2,5,15,17},
  {2,3,6,16,18},
  {3,4,7,17,19},
  {4,5,8,18,20},
  {0,5,6,9,19},
  {1,6,7,10,20},
  {0,2,7,8,11},
  {1,3,8,9,12},
  {2,4,9,10,13},
  {3,5,10,11,14},
  {4,6,11,12,15},
  {5,7,12,13,16},
  {6,8,13,14,17},
  {7,9,14,15,18},
  {8,10,15,16,19},
  {9,11,16,17,20},
  {0,10,12,17,18},
  {1,11,13,18,19},
  {2,12,14,19,20},
  {0,3,13,15,20}]

theorem relation : ∀ a b : V, b ∈ neighbors a ↔ oriented a b ∨ oriented b a := by decide +kernel
theorem thin : ∀ c d : V, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1 := by decide +kernel
theorem total : target.card = 105 := by decide +kernel

private theorem edgeOK (a b : V) (mem : edge a b ∈ target) : b ∈ neighbors a := by
  have ok : oriented (min a b) (max a b) := (Finset.mem_filter.mp mem).2
  rw [relation]
  by_cases le : a ≤ b
  · exact .inl (by simpa [min_eq_left le,max_eq_right le] using ok)
  · have rev := le_of_not_ge le
    exact .inr (by simpa [min_eq_right rev,max_eq_left rev] using ok)

def rectangle (A B : Finset V) : Finset E := A.biUnion fun a => B.image (edge a)

theorem rectSwap (A B : Finset V) : rectangle A B = rectangle B A := by
  ext e
  simp only [rectangle,Finset.mem_biUnion,Finset.mem_image]
  constructor <;> rintro ⟨a,ha,b,hb,h⟩ <;> exact ⟨b,hb,a,ha,(edgeSymm _ _).trans h⟩

private theorem oneCenter {A B : Finset V} (a : V) (hA : A = {a})
    (sub : rectangle A B ⊆ target) : B ⊆ neighbors a ∧ rectangle A B = B.image (edge a) := by
  subst A
  simpa [rectangle] using (show (B ⊆ neighbors a) ∧ rectangle {a} B = B.image (edge a) from by
    refine ⟨fun b hb => edgeOK _ _ (sub ?_), by simp [rectangle]⟩
    exact Finset.mem_biUnion.mpr ⟨a,by simp,Finset.mem_image_of_mem _ hb⟩)

private theorem oneOrEmpty {A : Finset V} (h : A.card ≤ 1) :
    A = ∅ ∨ ∃ a, A = {a} := by
  by_cases empty : A = ∅
  · exact .inl empty
  · exact .inr (Finset.card_eq_one.mp (by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega))

/-- Every sound rectangle of two arbitrary input supports reduces to a star.
Overlaps, empty supports, and operands containing both point and line variables are permitted. -/
theorem rectangleStar {B : Finset (Finset V)} {A D : Finset V} (ha : A ∈ B) (hd : D ∈ B)
    (sub : rectangle A D ⊆ target) :
    ∃ S ∈ B, ∃ c : V, S ⊆ neighbors c ∧ rectangle A D = S.image (edge c) := by
  have directed {a d} (aa : a ∈ A) (dd : d ∈ D) : d ∈ neighbors a :=
    edgeOK a d (sub (Finset.mem_biUnion.mpr ⟨a,aa,Finset.mem_image_of_mem _ dd⟩))
  by_cases smallA : A.card ≤ 1
  · rcases oneOrEmpty smallA with rfl | ⟨a,eq⟩
    · exact ⟨∅,ha,0,by simp,by simp [rectangle]⟩
    · exact ⟨D,hd,a,oneCenter a eq sub⟩
  · have two := Finset.one_lt_card.mp (by omega : 1 < A.card)
    obtain ⟨a,aa,b,bb,ne⟩ := two
    have enclosed : D ⊆ neighbors a ∩ neighbors b := fun d mem =>
      Finset.mem_inter.mpr ⟨directed aa mem,directed bb mem⟩
    have smallD := (Finset.card_le_card enclosed).trans (thin a b ne)
    rw [rectSwap] at sub ⊢
    rcases oneOrEmpty smallD with rfl | ⟨d,eq⟩
    · exact ⟨∅,hd,0,by simp,by simp [rectangle]⟩
    · exact ⟨A,ha,d,oneCenter d eq sub⟩

/-- Only subcircuits whose edge sets are contained in the target need to be charged. -/
private theorem outerForTarget {start bank : Finset (Finset E)} {k : ℕ}
    (run : Joins start k bank) {P : Finset E} (base : ∀ S ∈ start, S ⊆ target → almost S P) :
    ∃ Q : Finset E, Q.card ≤ P.card+k ∧ ∀ S ∈ bank, S ⊆ target → almost S Q := by
  induction run with
  | start => exact ⟨P,by omega,base⟩
  | @step k bank a b run ha hb ih =>
    obtain ⟨old,budget,ok⟩ := ih
    by_cases sound : a ∪ b ⊆ target
    · obtain ⟨new,inc,sz,both⟩ := repair (ok a ha (Finset.subset_union_left.trans sound))
        (ok b hb (Finset.subset_union_right.trans sound))
      refine ⟨new,by omega,?_⟩
      intro S hs ht
      rcases Finset.mem_insert.mp hs with rfl | prior
      · exact both
      · apply le_trans (Finset.card_le_card ?_) (ok S prior ht)
        intro e he
        obtain ⟨eS,en⟩ := Finset.mem_sdiff.mp he
        exact Finset.mem_sdiff.mpr ⟨eS, fun h => en (inc h)⟩
    · refine ⟨old,by omega,?_⟩
      intro S hs ht
      rcases Finset.mem_insert.mp hs with rfl | prior
      · exact (sound ht).elim
      · exact ok S prior ht

theorem rectangleORLower {initial inputBank : Finset (Finset V)} {products outputBank : Finset (Finset E)}
    {i o : ℕ} (seeds : ∀ S ∈ initial, S.card ≤ 1) (pre : Joins initial i inputBank)
    (middle : ∀ R ∈ products, ∃ A ∈ inputBank, ∃ B ∈ inputBank, R = rectangle A B)
    (post : Joins products o outputBank) (computes : target ∈ outputBank) : 104 ≤ i+o := by
  obtain ⟨P,sz,ok⟩ := inner neighbors edge thin seeds pre
  have base (R) (hr : R ∈ products) (valid : R ⊆ target) : almost R P := by
    obtain ⟨A,ha,B,hb,rfl⟩ := middle R hr
    obtain ⟨S,hs,c,sub,eq⟩ := rectangleStar ha hb valid
    rw [eq]
    exact ok S hs c sub
  obtain ⟨Q,hQ,final⟩ := outerForTarget post base
  have one := final target computes (by rfl)
  have sub : target ⊆ Q ∪ (target \ Q) := by
    intro e he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have count := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  unfold almost at one
  rw [total] at count
  omega

end Row4201.RectanglePlane
#print axioms Row4201.RectanglePlane.rectangleORLower
