import Mathlib

namespace ProjectivePlaneConeCount

/-- An exhaustive cut capacity of ten and total cut weight 686 force seven
shared wires whenever a fanout decomposition yields at most 2^h factors. -/
theorem shared_lower {h factors : ℕ}
    (cover : 686 ≤ 10 * factors) (decomposition : factors ≤ 2 ^ h) : 7 ≤ h := by
  by_contra! few
  have pow_bound : 2 ^ h ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at pow_bound
  omega

/-- Counts outgoing operand occurrences in the trimmed augmented circuit.
`nodes` omits the final output. Each node contributes at least one use and
each shared node contributes a second one. -/
theorem cone_count {α : Type*} [DecidableEq α] (nodes : Finset α) (degree : α → ℕ)
    {g stored : ℕ} (allInputs : 26 + g ≤ nodes.card + 1)
    (used : ∀ v ∈ nodes, 1 ≤ degree v)
    (fanin : ∑ v ∈ nodes, degree v ≤ 2 * g)
    (shared : 7 ≤ (nodes.filter (fun v => 2 ≤ degree v)).card)
    (augmented : g ≤ stored + 1) : 31 ≤ stored := by
  have pointwise (v) (hv : v ∈ nodes) : 1 + (if 2 ≤ degree v then 1 else 0) ≤ degree v := by
    split_ifs <;> have := used v hv <;> omega
  have total := Finset.sum_le_sum pointwise
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.sum_boole] at total
  change nodes.card + (nodes.filter (fun v => 2 ≤ degree v)).card ≤ ∑ v ∈ nodes, degree v at total
  omega

#print axioms shared_lower
#print axioms cone_count

end ProjectivePlaneConeCount
