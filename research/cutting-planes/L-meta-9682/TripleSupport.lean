import GlobalRank

/-! A first Chvátal–Gomory cut for the pairwise pigeonhole relaxation holds
at every rowwise triple point. Each pigeon may choose a different injection
of three holes. The normalization and floor arithmetic follow PHPThird.globalRoundThird. -/
namespace PHPTriples

abbrev V (m : ℕ) := Fin m × Fin 3
abbrev Picks (m n : ℕ) := Fin m → Fin 3 ↪ Fin n

/-- Numerators at denominator two, with the unsupported coordinates zero. -/
def OnTriples {m n} (pick : Picks m n) (x : V m → ℤ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 2) ∧ (∀ i, ∑ j : Fin 3, x (i,j) = 2) ∧
  ∀ i k j l, i ≠ k → pick i j = pick k l → x (i,j) + x (k,l) ≤ 2


private theorem halfOK {m n} (pick : Picks m n) (k : Fin m → Fin 3) :
    OnTriples pick (PHPThird.half k) := by
  refine ⟨fun v => ?_, fun i => ?_, fun i t j l _ _ => ?_⟩
  · simp [PHPThird.half]; split <;> omega
  · generalize he : k i = j
    fin_cases j <;> simp [Fin.sum_univ_succ, PHPThird.half, he]
  · simp only [PHPThird.half]; split <;> split <;> omega

private noncomputable def avoid {m n} (pick : Picks m n) (h : Fin n) (i : Fin m) : Fin 3 :=
  if ht : ∃ j, pick i j = h then Classical.choose ht else 0

private theorem avoid_eq {m n} (pick : Picks m n) (h : Fin n) (i : Fin m) (j : Fin 3)
    (hj : pick i j = h) : avoid pick h i = j := by
  have he : ∃ l, pick i l = h := ⟨j,hj⟩
  simp only [avoid, dite_eq_left he]
  exact (pick i).injective ((Classical.choose_spec he).trans hj.symm)

private noncomputable def single {m n} (pick : Picks m n) (p v : V m) : ℤ :=
  if v.1 = p.1 then (if v.2 = p.2 then 2 else 0)
  else PHPThird.half (avoid pick (pick p.1 p.2)) v

private theorem singleOK {m n} (pick : Picks m n) (p : V m) :
    OnTriples pick (single pick p) := by
  refine ⟨fun v => ?_, fun i => ?_, fun i t j l ne same => ?_⟩
  · simp only [single,PHPThird.half]; split_ifs <;> omega
  · by_cases hi : i = p.1
    · simp [single,hi]
    · simpa [single,hi] using (halfOK pick (avoid pick (pick p.1 p.2))).2.1 i
  · by_cases hi : i = p.1
    · subst i
      have ht : t ≠ p.1 := Ne.symm ne
      by_cases hj : j = p.2
      · subst j
        simp [single,ht,PHPThird.half,avoid_eq pick _ _ l same.symm]
      · simp [single,hj,ht,PHPThird.half]; split <;> omega
    · by_cases ht : t = p.1
      · subst t
        by_cases hl : l = p.2
        · subst l
          simp [single,hi,PHPThird.half,avoid_eq pick _ _ j same]
        · simp [single,hi,hl,PHPThird.half]; split <;> omega
      · simpa [single,hi,ht] using
          (halfOK pick (avoid pick (pick p.1 p.2))).2.2 i t j l ne same

private theorem rowShift {m} (s : ℤ) (f : Fin m → ℤ) (x : V m → ℤ)
    (rows : ∀ i, ∑ j : Fin 3, x (i,j) = s) :
    (∑ v, f v.1 * x v) = s * ∑ i, f i := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, f i * x (i,j)) = s * f i
  rw [← Finset.mul_sum, rows, mul_comm]

private def argmin (r : Fin 3 → ℤ) : Fin 3 :=
  if r 0 ≤ r 1 ∧ r 0 ≤ r 2 then 0 else if r 1 ≤ r 2 then 1 else 2

private theorem minSpec (r : Fin 3 → ℤ) (j : Fin 3) : r (argmin r) ≤ r j := by
  fin_cases j
  · change r (argmin r) ≤ r 0
    unfold argmin; split_ifs <;> omega
  · change r (argmin r) ≤ r 1
    unfold argmin; split_ifs <;> omega
  · change r (argmin r) ≤ r 2
    unfold argmin; split_ifs <;> omega

/-- A valid upper inequality with integer post-division coefficients cannot
separate uniform thirds after its first rounding, irrespective of its support. -/
theorem supportedRound {m n} (pick : Picks m n) (a : V m → ℤ) (b d : ℤ) (hd : 0 < d)
    (valid : ∀ x : V m → ℤ, OnTriples pick x → d * (∑ v, a v * x v) ≤ 2*b) :
    (∑ v, a v) ≤ 3*(b/d) := by
  let k (i : Fin m) := argmin (fun j => a (i,j))
  let u (i : Fin m) := a (i,k i)
  let r (v : V m) := a v - u v.1
  let M := ∑ i, u i
  have nn (v : V m) : 0 ≤ r v := sub_nonneg.mpr (minSpec (fun j => a (v.1,j)) v.2)
  have shift {s : ℤ} (x : V m → ℤ) (rows : ∀ i, ∑ j : Fin 3, x (i,j) = s) :
      (∑ v, a v*x v) = (∑ v, r v*x v)+s*M := by
    rw [← rowShift s u x rows, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    simp only [r, sub_mul]; abel
  have reduced (x : V m → ℤ) (hx : OnTriples pick x) :
      d*(∑ v, r v*x v) ≤ 2*(b-d*M) := by
    have h := valid x hx
    rw [shift x hx.2.1] at h
    linarith only [h]
  have sums : (∑ v, r v * PHPThird.half k v) = ∑ v, r v := by
    apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ _
    by_cases e : j = k i
    · subst j; simp [r,u,PHPThird.half]
    · simp [PHPThird.half,e]
  have halfBound := reduced _ (halfOK pick k)
  rw [sums] at halfBound
  have nonnegSum : 0 ≤ ∑ v, r v := Finset.sum_nonneg (fun v _ => nn v)
  have h0 : 0 ≤ b-d*M := by have := mul_nonneg hd.le nonnegSum; linarith only [halfBound, this]
  have hs (p : V m) : d*r p ≤ b-d*M := by
    have ok := singleOK pick p
    have test := reduced _ ok
    have one : r p*2 ≤ ∑ v, r v*single pick p v := by
      simpa [single] using (Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (V m))) =>
        mul_nonneg (nn v) (ok.1 v).1) (Finset.mem_univ p))
    have mult := mul_le_mul_of_nonneg_left one hd.le
    linarith only [test, mult]
  have ht := CliqueCut.roundThird r hd h0 hs (by simpa only [max_eq_left (nn _)] using halfBound)
  rw [Int.sub_mul_ediv_left _ _ hd.ne'] at ht
  have all := shift (s := 3) (fun _ => (1:ℤ)) (by intro i; decide)
  simp only [mul_one] at all
  linarith only [all, ht]



/-- Half-integral feasible points of the full LP, written using doubled
coordinates. Pigeon rows may have sums greater than one. -/
def Feasible {m n} (x : Fin m × Fin n → ℤ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 2) ∧ (∀ i, 2 ≤ ∑ h : Fin n, x (i,h)) ∧
  ∀ i k h, i ≠ k → x (i,h) + x (k,h) ≤ 2

/-- Extend a supported point by zero on all unselected holes. -/
def extend {m n} (pick : Picks m n) (x : V m → ℤ) (v : Fin m × Fin n) : ℤ :=
  ∑ j : Fin 3, if pick v.1 j = v.2 then x (v.1,j) else 0

private theorem extendAt {m n} (pick : Picks m n) (x : V m → ℤ) (i : Fin m) (j : Fin 3) :
    extend pick x (i,pick i j) = x (i,j) := by
  simp [extend, (pick i).injective.eq_iff]

private theorem extendOff {m n} (pick : Picks m n) (x : V m → ℤ) (i : Fin m) (h : Fin n)
    (off : ¬ ∃ j, pick i j = h) : extend pick x (i,h) = 0 := by
  have hf : ∀ j, pick i j ≠ h := by simpa using off
  simp [extend,hf]

theorem feasibleExtend {m n} (pick : Picks m n) (x : V m → ℤ) (hx : OnTriples pick x) :
    Feasible (extend pick x) := by
  have bounds (i : Fin m) (h : Fin n) : 0 ≤ extend pick x (i,h) ∧ extend pick x (i,h) ≤ 2 := by
    by_cases hin : ∃ j, pick i j = h
    · obtain ⟨j,rfl⟩ := hin
      rw [extendAt]
      exact hx.1 (i,j)
    · rw [extendOff _ _ _ _ hin]
      omega
  refine ⟨fun ⟨i,h⟩ => bounds i h, ?_, ?_⟩
  · intro i
    simp only [extend]
    rw [Finset.sum_comm]
    simpa using (hx.2.1 i).ge
  · intro i k h ne
    by_cases hi : ∃ j, pick i j = h
    · obtain ⟨j,rfl⟩ := hi
      rw [extendAt]
      by_cases hk : ∃ l, pick k l = pick i j
      · obtain ⟨l, hl⟩ := hk
        rw [← hl, extendAt]
        exact hx.2.2 i k j l ne hl.symm
      · rw [extendOff _ _ _ _ hk, add_zero]
        exact (hx.1 _).2
    · rw [extendOff _ _ _ _ hi,zero_add]
      exact (bounds k h).2

private theorem dotExtend {m n} (pick : Picks m n) (a : Fin m × Fin n → ℤ) (x : V m → ℤ) :
    (∑ v, a v * extend pick x v) = ∑ v : V m, a (v.1,pick v.1 v.2) * x v := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ h : Fin n, a (i,h) * ∑ j : Fin 3, if pick i j = h then x (i,j) else 0) = _
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- If d·a·x ≤ b holds throughout the half-integral points of the actual
m-by-n pigeonhole relaxation, then its first integer rounding a·x ≤ ⌊b/d⌋
holds at the point putting one third on each of the three chosen cells per row. -/
theorem fullRound {m n} (pick : Picks m n) (a : Fin m × Fin n → ℤ) (b d : ℤ) (hd : 0 < d)
    (valid : ∀ x : Fin m × Fin n → ℤ, Feasible x → d * (∑ v, a v * x v) ≤ 2*b) :
    (∑ v : V m, a (v.1,pick v.1 v.2)) ≤ 3*(b/d) := by
  apply supportedRound pick _ b d hd
  intro x hx
  simpa only [dotExtend] using valid _ (feasibleExtend pick x hx)


/-- Averaging the translates of a three-hole support proves the corresponding
uniform-point statement for every number of holes at least three. -/
theorem uniformRound {m n : ℕ} (hn : 3 ≤ n) (a : Fin m × Fin n → ℤ) (b d : ℤ) (hd : 0 < d)
    (valid : ∀ x : Fin m × Fin n → ℤ, Feasible x → d * (∑ v, a v * x v) ≤ 2*b) :
    (∑ v, a v) ≤ (n : ℤ)*(b/d) := by
  let : NeZero n := ⟨by omega⟩
  let shift (h : Fin n) : Fin 3 ↪ Fin n := (Fin.castLEEmb hn).trans (Equiv.addLeft h).toEmbedding
  have hr (h : Fin n) := fullRound (fun _ : Fin m => shift h) a b d hd valid
  have all := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hr h)
  have permutes (v : V m) : (∑ h : Fin n, a (v.1, shift h v.2)) = ∑ h, a (v.1,h) := by
    exact Equiv.sum_comp (Equiv.addRight (Fin.castLE hn v.2)) (fun h => a (v.1,h))
  change (∑ h : Fin n, ∑ v : V m, a (v.1,shift h v.2)) ≤ _ at all
  rw [Finset.sum_comm] at all
  simp_rw [permutes] at all
  have totals : (∑ v : V m, ∑ h : Fin n, a (v.1,h)) = 3 * ∑ v, a v := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  rw [totals] at all
  apply (Int.mul_le_mul_left (by decide : (0 : ℤ) < 3)).mp
  simpa [mul_assoc, mul_left_comm, mul_comm] using all

end PHPTriples
#print axioms PHPTriples.fullRound
#print axioms PHPTriples.uniformRound
