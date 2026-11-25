import PEqualNP.Defs

/- James Adams. In PHP(6,5), the pigeon rows and all five-pigeon
   column capacities determine a unique real point. -/
namespace PHP65

private theorem tight {n : ℕ} (f : Fin n → ℝ) (bound : ℝ)
    (le : ∀ i, f i ≤ bound) (total : n * bound ≤ ∑ i, f i) :
    ∀ i, f i = bound := by
  have nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ bound - f i :=
    fun i _ => sub_nonneg.mpr (le i)
  have z : (∑ i, (bound - f i)) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg nn)
    rw [Finset.sum_sub_distrib]
    simpa using sub_nonpos.mpr total
  intro i
  exact (sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg nn).mp z i (Finset.mem_univ i))).symm

theorem five_pigeon_cuts_force_uniform (x : Fin 6 → Fin 5 → ℝ)
    (rows : ∀ p, 1 ≤ ∑ h, x p h)
    (five : ∀ p h, (∑ q, x q h) - x p h ≤ 1) :
    ∀ p h, x p h = 1 / 5 := by
  let col (h : Fin 5) := ∑ p, x p h
  have column_bound (h : Fin 5) : col h ≤ 6/5 := by
    have b := Finset.sum_le_sum (s := Finset.univ) (fun p _ => five p h)
    rw [Finset.sum_sub_distrib] at b
    change (∑ _ : Fin 6, col h) - col h ≤ (∑ _ : Fin 6, (1 : ℝ)) at b
    norm_num at b
    linarith
  have total : 6 ≤ ∑ h, col h := by
    have b := Finset.sum_le_sum (s := Finset.univ) (fun p _ => rows p)
    rw [Finset.sum_comm] at b
    simpa [col] using b
  have column_eq := tight col (6/5) column_bound (by norm_num; linarith)
  intro p h
  have s : ∑ q, (col h - x q h) = 6 := by
    rw [Finset.sum_sub_distrib]
    change (∑ _ : Fin 6, col h) - col h = 6
    norm_num [column_eq]
  have eq := tight (fun q => col h - x q h) 1 (fun q => five q h)
    (by rw [s]; norm_num)
  have at_p := eq p
  rw [column_eq h] at at_p
  linarith

end PHP65
