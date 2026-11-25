import PEqualNP.Outside.L_meta_9672

/-!
A live dependency trace for any occurrence in an official cutting-planes derivation.
This generalizes harshb16's construction for a contradiction in merged L-meta-9672
(PR 16368, CPIntegrationScratch.exists_live_trace). The indices read the official
derivation in chronological order. Multiple occurrences of a line may have
different dependencies, so the indexed result allows choosing an occurrence.
-/
namespace CPTargetTrace

open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch

variable {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (CPLine V)}

/-- The live ancestors of a specified occurrence, including that occurrence itself. -/
theorem atIndex (derivation : IsCPDerivation F π) (root : ℕ) (inRange : root < π.length) :
    ∃ (rule : ℕ → Rule V) (live : Finset ℕ),
      root ∈ live ∧ live ⊆ Finset.range (root + 1) ∧ live.card ≤ π.length ∧
      (∀ i ∈ live, legalRule F i (earlier π) (earlier π i) (rule i)) ∧
      closedUnder (fun i => parents (rule i)) live ∧
      (∀ i j, j ∈ parents (rule i) → j < i) ∧
      ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j) := by
  obtain ⟨rs, trace⟩ := extract derivation
  let rule (i : ℕ) : Rule V :=
    if i < π.length then rs.reverse.getD i (.inl (.inl ∅)) else .inl (.inl ∅)
  have legal (i : ℕ) (hi : i < π.length) :
      legalRule F i (earlier π) (earlier π i) (rule i) := by
    have hir : i < rs.reverse.length := by simpa [trace_length trace] using hi
    have lookup : rs.reverse[i]? = some (rule i) := by
      simp [rule, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir]
    exact rule_at trace lookup
  have order (i j : ℕ) (hj : j ∈ parents (rule i)) : j < i := by
    by_cases hi : i < π.length
    · exact parent_lt (legal i hi) j hj
    · simp [rule, hi, parents] at hj
  obtain ⟨live, member, subset, closed, used⟩ := find_live _ root order
  refine ⟨rule, live, member, subset, ?_, ?_, closed, order, used⟩
  · have h := Finset.card_le_card subset
    simp only [Finset.card_range] at h
    omega
  · intro i hi
    have h := Finset.mem_range.mp (subset hi)
    exact legal i (by omega)

/-- Every target line in an official derivation has a closed, topologically
ordered trace of at most the length of that derivation. -/
theorem forLine (derivation : IsCPDerivation F π) {target : CPLine V} (occurs : target ∈ π) :
    ∃ (root : ℕ) (rule : ℕ → Rule V) (live : Finset ℕ),
      root < π.length ∧ earlier π root = target ∧
      root ∈ live ∧ live ⊆ Finset.range (root + 1) ∧ live.card ≤ π.length ∧
      (∀ i ∈ live, legalRule F i (earlier π) (earlier π i) (rule i)) ∧
      closedUnder (fun i => parents (rule i)) live ∧
      (∀ i j, j ∈ parents (rule i) → j < i) ∧
      ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j) := by
  obtain ⟨root, inRange, read⟩ := find_earlier occurs
  obtain ⟨rule, live, properties⟩ := atIndex derivation root inRange
  exact ⟨root, rule, live, inRange, read, properties⟩

end CPTargetTrace

#print axioms CPTargetTrace.atIndex
#print axioms CPTargetTrace.forLine
