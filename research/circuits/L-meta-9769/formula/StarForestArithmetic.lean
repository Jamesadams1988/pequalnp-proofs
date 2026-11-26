import Mathlib

namespace PuncturedPlane.StarForest

theorem one_incidence_charge (d : ℕ) : d ≤ 1 + d.choose 2 := by
  cases d with
  | zero => decide
  | succ n =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

theorem two_incidence_charge (d : ℕ) : 2 * d ≤ 3 + d.choose 2 := by
  cases d with
  | zero => decide
  | succ n =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    change 2 * (n+1) ≤ 3 + (n + n.choose 2)
    have h := one_incidence_charge n
    omega

/-- The incidence and pair bounds are incompatible with 26 selected vertices. -/
theorem numeric_exclusion (k D B : ℕ) (hk₀ : 5 ≤ k) (hk₁ : k ≤ 13)
    (hD : 5*k ≤ 26+D) (hB : B ≤ (k-5).choose 2)
    (hfirst : D ≤ k+B) (hsecond : 2*D ≤ 3*k+B)
    (hsmall : k ≤ 6 → k.choose 2 ≤ 4+10*(k-5)) : False := by
  interval_cases k <;> norm_num [Nat.choose] at * <;> omega

/-- Here d(i) is the number of omitted opposite vertices incident to selected vertex i. -/
theorem exclude_from_local_counts (k : ℕ) (d : Fin k → ℕ) (hk₀ : 5 ≤ k) (hk₁ : k ≤ 13)
    (hD : 5*k ≤ 26 + ∑ i, d i)
    (hB : (∑ i, (d i).choose 2) ≤ (k-5).choose 2)
    (hsmall : k ≤ 6 → k.choose 2 ≤ 4+10*(k-5)) : False := by
  have hFirst := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => one_incidence_charge (d i))
  have hSecond := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => two_incidence_charge (d i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one] at hFirst hSecond
  rw [← Finset.mul_sum] at hSecond
  exact numeric_exclusion k _ _ hk₀ hk₁ hD hB hFirst (by simpa [Nat.mul_comm] using hSecond) hsmall

#print axioms exclude_from_local_counts
end PuncturedPlane.StarForest
