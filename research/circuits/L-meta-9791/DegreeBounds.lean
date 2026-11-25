import Extension
import PEqualNP.Outside.L_meta_1500
import PEqualNP.Outside.L_meta_2145

/-! Restrictions on the syntactic degrees of any 53-gate solution to L-meta-9791. -/
namespace PartialPlaneExtension
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def pointInc (p w : Fin 13) : Prop :=
  ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d

private theorem convertInc (p w : Fin 13) : OfficialInc p w ↔ pointInc p w := by
  have allPairs : ∀ a b : Fin 13, inc a b = true ↔ pointInc a b := by
    unfold pointInc
    decide +kernel
  exact (inc_iff p w).trans (allPairs p w)

/-- Exact full plane incidence implies the positive and negative tests of L-meta-2145. -/
theorem point_obstruction (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ fullFn x) :
    63 < C.size ∨ 1 < C.lineDeg 26 (Finset.range 13) := by
  by_contra! small
  rcases small with ⟨size,degree⟩
  apply PEqualNP.Outside.L_meta_2145
  refine ⟨C,mono,size,degree,?_,?_⟩
  · intro p w edge
    apply (correct _).mpr
    refine ⟨p,w,(convertInc p w).mpr edge,?_,?_⟩
    · exact decide_eq_true (Or.inl rfl)
    · exact decide_eq_true (Or.inr rfl)
  · intro S _outside _nonconcurrent
    apply Bool.eq_false_iff.mpr
    intro hx
    obtain ⟨p,w,inc,hp,hw⟩ := (correct _).mp hx
    change decide _ = true at hp hw
    simp only [decide_eq_true_eq] at hp hw
    have sep : ∀ a b : Fin 13, Fin.castAdd 13 a ≠ Fin.natAdd 13 b := by decide +kernel
    have lInj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := by decide +kernel
    have rInj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := by decide +kernel
    obtain ⟨u,mu,eu⟩ | ⟨l,el,_⟩ := hp
    · have ep := lInj eu
      subst u
      obtain ⟨v,_,ev⟩ | ⟨k,ek,indep⟩ := hw
      · exact sep v w ev.symm
      · have ew := rInj ek
        subst k
        exact indep p mu ((convertInc p w).mp inc)
    · exact sep p l el

/-- A circuit of size at most 53 for the listed 24-input graph must be nonlinear on point inputs. -/
theorem small_point_degree (C : Circuit) (mono : Monotone2 C) (hsize : C.size ≤ 53)
    (correct : ∀ x : Fin 24 → Bool, C.eval (List.ofFn x) = true ↔ oldFn x) :
    1 < C.lineDeg 24 (Finset.range 13) := by
  have h := point_obstruction (extension C) (mono_extension mono) (extension_graph C correct)
  rcases h with big | nonlinear
  · rw [size_extension] at big
    omega
  · change 1 < (extension C).lineDeg 26 (marks 26 false) at nonlinear
    rw [extension_degree] at nonlinear
    change 1 < max 1 (C.lineDeg 24 (Finset.range 13)) at nonlinear
    omega

/-- A circuit of size at most 53 must also be nonlinear on line inputs. -/
theorem small_line_degree (C : Circuit)
    (mono : Monotone2 C) (small : C.size ≤ 53)
    (solves : ∀ z : Fin 24 → Bool, C.eval (List.ofFn z) = true ↔ oldFn z) :
    2 ≤ C.lineDeg 24 (Finset.Ico 13 24) := by
  by_contra! h
  apply PEqualNP.Outside.L_meta_1500
  refine ⟨extension C, mono_extension mono, ?_, ?_, ?_, ?_⟩
  · rw [size_extension]; omega
  · change (extension C).lineDeg 26 (marks 26 true) ≤ 1
    rw [extension_degree]
    change max 1 (C.lineDeg 24 (Finset.Ico 13 24)) ≤ 1
    omega
  · intro x _ ev; exact (extension_graph C solves x).1 ev
  · intro p w hi
    apply (extension_graph C solves _).2
    exact ⟨p,w,hi,by simp,by simp⟩

theorem degree_bounds (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 53)
    (correct : ∀ z : Fin 24 → Bool, C.eval (List.ofFn z) = true ↔ oldFn z) :
    2 ≤ C.lineDeg 24 (Finset.range 13) ∧ 2 ≤ C.lineDeg 24 (Finset.Ico 13 24) :=
  ⟨small_point_degree C mono small correct, small_line_degree C mono small correct⟩

#print axioms degree_bounds
end PartialPlaneExtension
