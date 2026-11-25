import PEqualNP.Defs

/-! A unique rectangle separating two rows of the assigned matrix has collinear
row support. The dual argument applies to column supports. -/
namespace RectanglePencilDifference

abbrev V := Fin 31
abbrev Rect := Finset V × Finset V

def entry (p l : V) : Bool := (([1141899472, 136315297, 272630594, 545261188,
  1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360,
  427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344,
  109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369,
  554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] :
  List ℕ).getD p.val 0).testBit l.val

def Sound (M : V → V → Bool) (L : List Rect) : Prop :=
  ∀ R ∈ L, ∀ p ∈ R.1, ∀ l ∈ R.2, M p l = false

def Covers (M : V → V → Bool) (L : List Rect) : Prop :=
  ∀ p l, M p l = false → ∃ R ∈ L, p ∈ R.1 ∧ l ∈ R.2

def Collinear (M : V → V → Bool) (A : Finset V) : Prop :=
  ∃ l, ∀ p ∈ A, M p l = true

def PlanePairs (M : V → V → Bool) : Prop :=
  ∀ p q, p ≠ q → ∃ l, (M p l = true ∧ M q l = true) ∧
    ∀ j, (M p j = true ∧ M q j = true) → j = l

/-- If all rectangles covering p but omitting q agree on R, its row support lies
on the line through p and q. This theorem also handles a row with any degree. -/
theorem unique_difference_collinear {M : V → V → Bool}
    (plane : PlanePairs M) {L : List Rect} (sound : Sound M L) (cover : Covers M L)
    {p q : V} (pq : p ≠ q) {R : Rect}
    (unique : ∀ T ∈ L, p ∈ T.1 → q ∉ T.1 → T = R) :
    Collinear M R.1 := by
  obtain ⟨j, hpq, only⟩ := plane p q pq
  refine ⟨j, ?_⟩
  intro x hx
  by_cases xq : x = q
  · simpa [xq] using hpq.2
  obtain ⟨k, hk, _⟩ := plane x q xq
  cases hp : M p k with
  | true =>
    have hkj := only k ⟨hp, hk.2⟩
    simpa [hkj] using hk.1
  | false =>
    obtain ⟨T, hT, hpt, hkt⟩ := cover p k hp
    have hqt : q ∉ T.1 := by
      intro hq
      have h := sound T hT q hq k hkt
      simp [hk.2] at h
    have htr := unique T hT hpt hqt
    subst T
    have h := sound R hT x hx k hkt
    simp [hk.1] at h

/-- A noncollinear-only cover separates every ordered row pair twice. -/
theorem two_differences {M : V → V → Bool}
    (plane : PlanePairs M) {L : List Rect} (sound : Sound M L) (cover : Covers M L)
    (noncollinear : ∀ R ∈ L, ¬ Collinear M R.1)
    (separates : ∀ p q : V, p ≠ q → ∃ l, M p l = false ∧ M q l = true)
    {p q : V} (pq : p ≠ q) :
    ∃ R ∈ L, ∃ T ∈ L, R ≠ T ∧ p ∈ R.1 ∧ p ∈ T.1 ∧ q ∉ R.1 ∧ q ∉ T.1 := by
  obtain ⟨j,hp,hq⟩ := separates p q pq
  obtain ⟨R,hR,hpR,hjR⟩ := cover p j hp
  have hqR : q ∉ R.1 := by
    intro h; have := sound R hR q h j hjR; simp [hq] at this
  by_contra! h
  apply noncollinear R hR
  apply unique_difference_collinear plane sound cover pq
  intro T hT hpT hqT
  by_contra ne
  exact hqT (h R hR T hT (Ne.symm ne) hpR hpT hqR)

set_option maxRecDepth 32000 in
theorem entry_separates : ∀ p q : V, p ≠ q →
    ∃ l, entry p l = false ∧ entry q l = true := by decide +kernel

set_option maxRecDepth 32000 in
theorem transpose_separates : ∀ p q : V, p ≠ q →
    ∃ l, entry l p = false ∧ entry l q = true := by decide +kernel

def lineRows (M : V → V → Bool) (j : V) : Finset V :=
  Finset.univ.filter (fun p => M p j = true)

def allowed (M : V → V → Bool) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun l => ∀ p ∈ A, M p l = false)

def PencilBound (M : V → V → Bool) : Prop :=
  ∀ j : V, ∀ A ∈ (lineRows M j).powerset, A.card * (allowed M A).card ≤ 45

theorem large_noncollinear {M : V → V → Bool} (pb : PencilBound M) {L : List Rect}
    (sound : Sound M L) {R : Rect} (hr : R ∈ L) (large : 45 < R.1.card * R.2.card) :
    ¬ Collinear M R.1 := by
  rintro ⟨j,hj⟩
  have sub : R.1 ⊆ lineRows M j := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj p hp⟩
  have sub' : R.2 ⊆ allowed M R.1 := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => sound R hr p hp l hl⟩
  exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_left _ (Finset.card_le_card sub')).trans
    (pb j R.1 (Finset.mem_powerset.mpr sub)))) large

theorem all_large_two {M : V → V → Bool} (plane : PlanePairs M) (pb : PencilBound M)
    (separates : ∀ p q : V, p ≠ q → ∃ l, M p l = false ∧ M q l = true)
    {L : List Rect} (sound : Sound M L) (cover : Covers M L)
    (large : ∀ R ∈ L, 45 < R.1.card * R.2.card) {p q : V} (pq : p ≠ q) :
    ∃ R ∈ L, ∃ T ∈ L, R ≠ T ∧ p ∈ R.1 ∧ p ∈ T.1 ∧ q ∉ R.1 ∧ q ∉ T.1 :=
  two_differences plane sound cover
    (fun _ h => large_noncollinear pb sound h (large _ h)) separates pq

#print axioms RectanglePencilDifference.all_large_two
end RectanglePencilDifference
