import RankOne

/-! Uniform thirds survives the first cutting-plane closure for any number of
pigeons and three holes, even for cuts mixing constraints from different holes. -/
namespace PHPThird
abbrev V (m : ℕ) := Fin m × Fin 3

/-- Numerators of LP-feasible assignments at denominator 2, with row sums exactly 2. -/
def Feasible {m} (x : V m → ℤ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 2) ∧ (∀ i : Fin m, ∑ j : Fin 3, x (i,j) = 2) ∧
  ∀ i k : Fin m, ∀ j : Fin 3, i ≠ k → x (i,j) + x (k,j) ≤ 2

def half {m} (k : Fin m → Fin 3) (v : V m) : ℤ := if v.2 = k v.1 then 0 else 1
def single {m} (p v : V m) : ℤ := if v.1 = p.1 then (if v.2 = p.2 then 2 else 0)
  else (if v.2 = p.2 then 0 else 1)

private theorem halfOK {m} (k : Fin m → Fin 3) : Feasible (half k) := by
  refine ⟨fun v => ?_, fun i => ?_, fun i l j _ => ?_⟩
  · simp [half]; split <;> omega
  · generalize he : k i = j
    fin_cases j <;> simp [Fin.sum_univ_succ,half,he]
  · simp only [half]; split <;> split <;> omega

private theorem singleOK {m} (p : V m) : Feasible (single p) := by
  refine ⟨fun v => ?_, fun i => ?_, fun i l j ne => ?_⟩
  · simp only [single]; split_ifs <;> omega
  · obtain ⟨a,k⟩ := p
    by_cases h : i = a <;> fin_cases k <;> simp [Fin.sum_univ_succ,single,h]
  · simp only [single]; split_ifs <;> grind

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
theorem globalRoundThird {m} (a : V m → ℤ) (b d : ℤ) (hd : 0 < d)
    (valid : ∀ x : V m → ℤ, Feasible x → d * (∑ v, a v * x v) ≤ 2*b) :
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
  have reduced (x : V m → ℤ) (hx : Feasible x) :
      d*(∑ v, r v*x v) ≤ 2*(b-d*M) := by
    have h := valid x hx
    rw [shift x hx.2.1] at h
    linarith only [h]
  have sums : (∑ v, r v * half k v) = ∑ v, r v := by
    apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ _
    by_cases e : j = k i
    · subst j; simp [r,u,half]
    · simp [half,e]
  have halfBound := reduced _ (halfOK k)
  rw [sums] at halfBound
  have nonnegSum : 0 ≤ ∑ v, r v := Finset.sum_nonneg (fun v _ => nn v)
  have h0 : 0 ≤ b-d*M := by have := mul_nonneg hd.le nonnegSum; linarith only [halfBound, this]
  have hs (p : V m) : d*r p ≤ b-d*M := by
    have ok := singleOK p
    have test := reduced _ ok
    have one : r p*2 ≤ ∑ v, r v*single p v := by
      simpa [single] using (Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (V m))) =>
        mul_nonneg (nn v) (ok.1 v).1) (Finset.mem_univ p))
    have mult := mul_le_mul_of_nonneg_left one hd.le
    linarith only [test, mult]
  have ht := CliqueCut.roundThird r hd h0 hs (by simpa only [max_eq_left (nn _)] using halfBound)
  rw [Int.sub_mul_ediv_left _ _ hd.ne'] at ht
  have all := shift (s := 3) (fun _ => (1:ℤ)) (by intro i; decide)
  simp only [mul_one] at all
  linarith only [all, ht]

end PHPThird
#print axioms PHPThird.globalRoundThird
