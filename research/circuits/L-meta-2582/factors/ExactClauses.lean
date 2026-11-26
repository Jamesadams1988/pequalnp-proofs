import FactorCount

/- James Adams. Exact number of positive clauses for a finite bipartite
   incidence function, counting distinct unions of neighborhoods. -/
namespace IncidenceReadTwo.FactorCount

open Finset
variable {P L J : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

def unions (nb : P → Finset L) : Finset (Finset L) :=
  univ.image (fun s : Finset P => s.biUnion nb)

def inside (nb : P → Finset L) (u : Finset L) : Finset P :=
  univ.filter (fun p => nb p ⊆ u)

omit [Fintype L] [DecidableEq P] in
private theorem inside_union {nb : P → Finset L} {u : Finset L} (hu : u ∈ unions nb) :
    (inside nb u).biUnion nb = u := by
  obtain ⟨s,_,rfl⟩ := mem_image.mp hu
  apply Subset.antisymm
  · intro l hl
    obtain ⟨p,hp,hl⟩ := mem_biUnion.mp hl
    exact (mem_filter.mp hp).2 hl
  · intro l hl
    obtain ⟨p,hp,hl⟩ := mem_biUnion.mp hl
    apply mem_biUnion.mpr
    exact ⟨p, mem_filter.mpr ⟨mem_univ _, fun _ h => mem_biUnion.mpr ⟨p,hp,h⟩⟩,hl⟩

def HasEdge (nb : P → Finset L) (s : Finset P) (t : Finset L) : Prop :=
  ∃ p ∈ s, ∃ l ∈ t, l ∈ nb p

omit [Fintype L] in
/-- One positive clause for each neighborhood union suffices. -/
theorem canonical_clauses (nb : P → Finset L) (s : Finset P) (t : Finset L) :
    HasEdge nb s t ↔ ∀ u ∈ unions nb, Hit (univ \ inside nb u) u s t := by
  classical
  constructor
  · rintro ⟨p,hp,l,hl,he⟩ u _
    by_cases h : l ∈ u
    · exact Or.inr ⟨l,hl,h⟩
    · exact Or.inl ⟨p,hp,mem_sdiff.mpr ⟨mem_univ _,fun hh => h ((mem_filter.mp hh).2 he)⟩⟩
  · intro all
    have hu : s.biUnion nb ∈ unions nb := mem_image.mpr ⟨s,mem_univ _,rfl⟩
    rcases all _ hu with ⟨p,hp,hout⟩ | ⟨l,hl,hn⟩
    · have hi : p ∈ inside nb (s.biUnion nb) :=
        mem_filter.mpr ⟨mem_univ _,fun _ h => mem_biUnion.mpr ⟨p,hp,h⟩⟩
      exact ((mem_sdiff.mp hout).2 hi).elim
    · obtain ⟨p,hp,he⟩ := mem_biUnion.mp hn
      exact ⟨p,hp,l,hl,he⟩

omit [DecidableEq P] in
/-- A single clause cannot reject the maximal false inputs for two different
    neighborhood unions. Hence every exact positive CNF needs this many clauses. -/
theorem clause_lower [Fintype J] (nb : P → Finset L)
    (ap : J → Finset P) (al : J → Finset L)
    (correct : ∀ s t, HasEdge nb s t ↔ ∀ j, Hit (ap j) (al j) s t) :
    (unions nb).card ≤ Fintype.card J := by
  classical
  have misses (u : {z // z ∈ unions nb}) :
      ∃ j, ¬ Hit (ap j) (al j) (inside nb u.val) (univ \ u.val) := by
    by_contra! all
    obtain ⟨p,hp,l,hl,he⟩ := (correct _ _).mpr all
    exact (mem_sdiff.mp hl).2 ((mem_filter.mp hp).2 he)
  choose witness hw using misses
  have sub (u v : {z // z ∈ unions nb}) (eq : witness u = witness v) : u.val ⊆ v.val := by
    intro l hlu
    by_contra hlv
    have h := inside_union u.property
    rw [← h] at hlu
    obtain ⟨p,hp,he⟩ := mem_biUnion.mp hlu
    have edge : HasEdge nb {p} {l} := ⟨p,by simp,l,by simp,he⟩
    rcases (correct _ _).mp edge (witness u) with ⟨a,ha,ha'⟩ | ⟨b,hb,hb'⟩
    · have e : a = p := mem_singleton.mp ha
      subst a
      exact hw u (Or.inl ⟨p,hp,ha'⟩)
    · have e : b = l := mem_singleton.mp hb
      subst b
      rw [eq] at hb'
      exact hw v (Or.inr ⟨l,mem_sdiff.mpr ⟨mem_univ _,hlv⟩,hb'⟩)
  have inject : Function.Injective witness := fun _ _ e =>
    Subtype.ext (Subset.antisymm (sub _ _ e) (sub _ _ e.symm))
  simpa using Fintype.card_le_of_injective witness inject

end IncidenceReadTwo.FactorCount
#print axioms IncidenceReadTwo.FactorCount.canonical_clauses
#print axioms IncidenceReadTwo.FactorCount.clause_lower
