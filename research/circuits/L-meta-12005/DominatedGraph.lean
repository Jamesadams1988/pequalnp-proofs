import ExactMinimum
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
A strict inclusion of open neighborhoods supplies a three-gate restriction for the
edge-detection function of a finite simple graph. A neighbor of q outside N(p)
witnesses q's essentiality in both p-branches. With q selected, an edge incident
with p can use q in its place, so these branches have the same cofactor.

Dependencies are Lean 4.36.0, the project's pinned Mathlib and the module
ExactMinimum from research/circuits/L-meta-12005 at research commit
9cf63b54efb5664b9dccb5b73a49cbdc738ea8b8. That module provides
LeafTransfer.threeGateRestriction for the unrestricted fan-in-two circuit model.
-/

open LeafTransfer PEqualNP.MetaComplexity

namespace DominatedGraph

/-- The Boolean function detecting an edge among the vertices set to true. -/
def edgeFunction {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (x : Fin m → Bool) : Bool :=
  decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)

variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

private def singletonInput (v : Fin m) (i : Fin m) : Bool := decide (i = v)

private theorem singletonOff (v : Fin m) : edgeFunction G (singletonInput v) = false := by
  simp [edgeFunction, singletonInput]

private theorem pairOn {u v : Fin m} (h : G.Adj u v) :
    edgeFunction G (Function.update (singletonInput v) u true) = true := by
  apply decide_eq_true
  exact ⟨u, v, h, by simp, by simp [Function.update_of_ne h.ne.symm, singletonInput]⟩

private theorem endpointEssential {u v : Fin m} (h : G.Adj u v) :
    essential (edgeFunction G) u := by
  refine ⟨singletonInput v, ?_⟩
  have hu : singletonInput v u = false := by simp [singletonInput, h.ne]
  rw [hu, Bool.not_false, pairOn G h, singletonOff G]
  decide

private theorem endpointCoreNonconstant {u v : Fin m} (h : G.Adj u v) :
    nonconstant (pin (edgeFunction G) u true) := by
  refine ⟨singletonInput u, singletonInput v, ?_⟩
  have hu : Function.update (singletonInput u) u true = singletonInput u := by
    funext i
    by_cases hi : i = u <;> simp [Function.update, singletonInput, hi]
  simp only [pin, hu, singletonOff G, pairOn G h]
  decide

private theorem neighborEssential {p q r : Fin m} (pq : p ≠ q) (pr : p ≠ r) (qr : G.Adj q r) (noEdge : ¬ G.Adj p r)
    (b : Bool) : essential (pin (edgeFunction G) p b) q := by
  let x : Fin m → Bool := fun i => decide (i = r)
  have qr_ne : q ≠ r := qr.ne
  have off : pin (edgeFunction G) p b x = false := by
    simp only [pin, edgeFunction, decide_eq_false_iff_not]
    rintro ⟨i, j, hij, hi, hj⟩
    have support (k : Fin m) (hk : Function.update x p b k = true) : k = p ∨ k = r := by
      by_cases h : k = p
      · exact Or.inl h
      · exact Or.inr (by simpa [x, Function.update_of_ne h] using hk)
    rcases support i hi with rfl | rfl <;> rcases support j hj with rfl | rfl
    · exact G.irrefl hij
    · exact noEdge hij
    · exact noEdge hij.symm
    · exact G.irrefl hij
  have on : pin (edgeFunction G) p b (Function.update x q (!x q)) = true := by
    simp only [pin, edgeFunction, decide_eq_true_eq]
    exact ⟨q, r, qr, by simp [Function.update_of_ne pq.symm, x, qr_ne],
      by simp [Function.update_of_ne pr.symm, Function.update_of_ne qr_ne.symm, x]⟩
  exact ⟨x, by rw [on, off]; decide⟩

/-- Once q is true, a selected edge incident with p can use q in place of p. -/
private theorem pinDominated {p q : Fin m} (different : p ≠ q) (dom : G.neighborSet p ⊆ G.neighborSet q)
    (b : Bool) : pin (pin (edgeFunction G) p b) q true = pin (edgeFunction G) q true := by
  funext x
  let transfer (u v : Fin m → Bool) (selected : v q = true)
      (same : ∀ i, i ≠ p → u i = v i) :
      (∃ i j, G.Adj i j ∧ u i = true ∧ u j = true) →
      (∃ i j, G.Adj i j ∧ v i = true ∧ v j = true) := by
    rintro ⟨i, j, edge, hi, hj⟩
    by_cases ip : i = p
    · subst i
      exact ⟨q, j, dom edge, selected, (same j edge.ne').symm.trans hj⟩
    by_cases jp : j = p
    · subst j
      exact ⟨q, i, dom edge.symm, selected, (same i ip).symm.trans hi⟩
    exact ⟨i, j, edge, (same i ip).symm.trans hi, (same j jp).symm.trans hj⟩
  unfold pin edgeFunction
  apply decide_eq_decide.mpr
  constructor
  · apply transfer
    · simp
    · intro i hi
      simp [Function.update_of_ne hi]
  · apply transfer
    · simp [Function.update_of_ne different.symm]
    · intro i hi
      simp [Function.update_of_ne hi]

/-- If p has a neighbor and its open neighborhood is strictly contained in q's,
fixing q to true saves at least three gates in the unrestricted fan-in-two model. -/
theorem threeGateRestriction_of_neighborSet_ssubset {n s : ℕ}
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] {p q : Fin (n + 1)}
    (hp : (G.neighborSet p).Nonempty) (hsub : G.neighborSet p ⊂ G.neighborSet q)
    (c : HasCircuitSize (n + 1) (edgeFunction G) s) :
    ∃ t, t + 3 ≤ s ∧ HasCircuitSize (n + 1) (pin (edgeFunction G) q true) t := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨r, hr, hpr⟩ := Set.exists_of_ssubset hsub
  have pq : p ≠ q := fun h => hsub.ne (congrArg G.neighborSet h)
  have noPQ : ¬ G.Adj p q := fun h => G.irrefl (hsub.le h)
  have qr : G.Adj q r := hr
  have pr : p ≠ r := fun h => noPQ (h ▸ qr.symm)
  exact threeGateRestriction (endpointEssential G ha)
    (neighborEssential G pq pr qr hpr) (pinDominated G pq hsub.le)
    (endpointCoreNonconstant G qr) c

end DominatedGraph

#print axioms DominatedGraph.threeGateRestriction_of_neighborSet_ssubset
