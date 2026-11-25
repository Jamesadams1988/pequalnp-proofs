import ForestBridge

namespace ForestIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def NoRectangle {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l')

def ShortCycle {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∃ (v : Fin (N+N)) (w : (graph I).Walk v v), w.IsCycle ∧ w.length < 7

def NearBranches {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∃ u v : Fin (N+N), u ≠ v ∧ 3 ≤ ((graph I).neighborSet u).ncard ∧
    3 ≤ ((graph I).neighborSet v).ncard ∧ ∃ w : (graph I).Walk u v, w.length < 7

def Normalizable {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∀ C : Circuit, Monotone2 C → ReadsBack (N+N) C →
    (∀ x : Fin (N+N) → Bool, circuitFun (N+N) C x = true ↔ incidence I x) →
    ∃ D, Normal I C D

/-- Only cyclic incidence graphs remain: a short cycle, or separated-from-short-cycles
    graphs containing a short walk between two distinct branch vertices. -/
theorem remaining_cases
    (short_cycles : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I],
      NoRectangle I → ShortCycle I → Normalizable I)
    (near_branches : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I],
      NoRectangle I → ¬(graph I).IsAcyclic → ¬ShortCycle I → NearBranches I → Normalizable I)
    {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hrect : NoRectangle I) : Normalizable I := by
  classical
  by_cases hf : (graph I).IsAcyclic
  · intro C hm _ hc
    exact forest_normalization I C hf hm hc
  by_cases hs : ShortCycle I
  · exact short_cycles I hrect hs
  by_cases hh : NearBranches I
  · exact near_branches I hrect hf hs hh
  intro C hm _ hc
  apply long_thread_normalization I C _ _ hm hc
  · intro v w hw
    exact le_of_not_gt (fun h => hs ⟨v,w,hw,h⟩)
  · intro u v huv hu hv w
    exact le_of_not_gt (fun h => hh ⟨u,v,huv,hu,hv,w,h⟩)

end ForestIncidence
