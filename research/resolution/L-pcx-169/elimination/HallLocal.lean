import PEqualNP.Defs

namespace Row169.HallLocal

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- Binary joins counted after the entire local stock has been made available. -/
inductive Joined (stock : Finset (Clause V)) : Nat → List (Clause V) → Prop
  | start : Joined stock 0 stock.toList
  | step {n π A B R} : Joined stock n π → A ∈ π → B ∈ π → IsResolvent A B R →
      Joined stock (n + 1) (R :: π)

private theorem unsat_parent {A B R : Clause V} (h : IsResolvent A B R) (a : V → Bool)
    (hr : ¬ ClauseSat a R) : ¬ ClauseSat a A ∨ ¬ ClauseSat a B := by
  obtain ⟨v, _, _, rfl⟩ := h
  cases hv : a v with
  | false =>
    left
    rintro ⟨l, hl, hs⟩
    refine hr ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
    rintro rfl
    simp [hv] at hs
  | true =>
    right
    rintro ⟨l, hl, hs⟩
    refine hr ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
    rintro rfl
    simp [hv] at hs

private theorem frontier {stock : Finset (Clause V)}
    (a : Clause V → V → Bool)
    (unique : ∀ c ∈ stock, ∀ d ∈ stock, ¬ ClauseSat (a c) d → c = d)
    {n π} (built : Joined stock n π) :
    ∀ fr : Finset (Clause V), (∀ d ∈ fr, d ∈ π) →
    (∀ c ∈ stock, ∃ d ∈ fr, ¬ ClauseSat (a c) d) → stock.card ≤ n + fr.card := by
  induction built with
  | start =>
    intro fr listed hit
    rw [Nat.zero_add]
    apply Finset.card_le_card
    intro c hc
    obtain ⟨d, hd, bad⟩ := hit c hc
    have hds : d ∈ stock := Finset.mem_toList.mp (listed d hd)
    rwa [unique c hc d hds bad]
  | @step n π A B R _ hA hB res ih =>
    intro fr listed hit
    by_cases hR : R ∈ fr
    · let fresh := insert A (insert B (fr.erase R))
      have listed' : ∀ d ∈ fresh, d ∈ π := by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | h
        · exact hA
        rcases Finset.mem_insert.mp h with rfl | h
        · exact hB
        obtain ⟨ne, mem⟩ := Finset.mem_erase.mp h
        exact (List.mem_cons.mp (listed _ mem)).resolve_left ne
      have hit' : ∀ c ∈ stock, ∃ d ∈ fresh, ¬ ClauseSat (a c) d := by
        intro c hc
        obtain ⟨d, hd, bad⟩ := hit c hc
        by_cases e : d = R
        · subst d
          rcases unsat_parent res (a c) bad with hb | hb
          · exact ⟨A, by simp [fresh], hb⟩
          · exact ⟨B, by simp [fresh], hb⟩
        · exact ⟨d, by simp [fresh, e, hd], bad⟩
      have hi := ih fresh listed' hit'
      have h1 := Finset.card_insert_le A (insert B (fr.erase R))
      have h2 := Finset.card_insert_le B (fr.erase R)
      have h3 := Finset.card_erase_of_mem hR
      have h4 := Finset.card_pos.mpr ⟨R,hR⟩
      dsimp [fresh] at hi
      omega
    · have listed' : ∀ d ∈ fr, d ∈ π := by
        intro d hd
        rcases List.mem_cons.mp (listed d hd) with e | h
        · subst d
          exact False.elim (hR hd)
        · exact h
      have := ih fr listed' hit
      omega

/-- A separate critical assignment for every premise forces one fewer binary joins
than there are premises, including with unrestricted reuse of intermediate lines. -/
theorem joinsNeeded {stock : Finset (Clause V)} {target : Clause V}
    (a : Clause V → V → Bool)
    (unique : ∀ c ∈ stock, ∀ d ∈ stock, ¬ ClauseSat (a c) d → c = d)
    (targetFalse : ∀ c ∈ stock, ¬ ClauseSat (a c) target)
    {n π} (built : Joined stock n π) (ht : target ∈ π) : stock.card ≤ n + 1 := by
  simpa using frontier a unique built {target}
    (by simpa using ht)
    (by simpa using targetFalse)

theorem joinsNeededOfModels {stock : Finset (Clause V)} {target : Clause V}
    (models : ∀ c ∈ stock, ∃ a : V → Bool, ¬ ClauseSat a target ∧
      ∀ d ∈ stock, ¬ ClauseSat a d → c = d)
    {n π} (built : Joined stock n π) (ht : target ∈ π) : stock.card ≤ n + 1 := by
  classical
  let a (c : Clause V) := if h : c ∈ stock then (models c h).choose else fun _ => false
  apply joinsNeeded a _ _ built ht
  · intro c hc d hd
    simpa [a, hc] using (models c hc).choose_spec.2 d hd
  · intro c hc
    simpa [a, hc] using (models c hc).choose_spec.1

end Row169.HallLocal
