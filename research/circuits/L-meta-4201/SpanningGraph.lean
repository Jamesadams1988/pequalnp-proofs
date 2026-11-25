import Charging

/-! A connected loopless graph can be numbered from an edge by adding one
vertex adjacent to an earlier vertex at each step. Such a numbering supplies
the charging witnesses below. The circuit may share earlier gates freely. -/
namespace Row4201.Charging
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem spanningOrder {m : ℕ} (edge : Fin (m+2) → Fin (m+2) → Prop)
    (loopless : ∀ v, ¬ edge v v)
    (touches : ∀ v, 0 < v.val → ∃ u, u.val < v.val ∧ (edge u v ∨ edge v u))
    (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔
      ∃ u v, edge u v ∧ x u = true ∧ x v = true) :
    m ≤ C.gates.countP isOr := by
  classical
  let fresh (k : Fin m) : Fin (m+2) := ⟨k.val+2, by omega⟩
  have neighbor (k : Fin m) := touches (fresh k) (by simp [fresh])
  choose prior smaller adjacent using neighbor
  let chain (t : ℕ) (v : Fin (m+2)) := decide (v.val < t+2)
  let pair (k : Fin m) (v : Fin (m+2)) := decide (v = prior k ∨ v = fresh k)
  refine lower C hm m chain pair ?_ ?_ ?_
  · intro i j h v hv
    simp only [chain,decide_eq_true_eq] at *
    omega
  · intro k
    have first := touches (1 : Fin (m+2)) (by simp)
    obtain ⟨u,hu,huv⟩ := first
    have oneVal : (1 : Fin (m+2)).val = 1 := by simp
    have onU : chain k.val u = true := by simp only [chain,decide_eq_true_eq]; omega
    have onOne : chain k.val 1 = true := by simp [chain]
    have onPair (v : Fin (m+2)) (h : v = prior k ∨ v = fresh k) : pair k v = true :=
      decide_eq_true h
    refine ⟨(computes _).mpr ?_, (computes _).mpr ?_, ?_⟩
    · rcases huv with h | h
      · exact ⟨u,1,h,onU,onOne⟩
      · exact ⟨1,u,h,onOne,onU⟩
    · rcases adjacent k with h | h
      · exact ⟨prior k,fresh k,h,onPair _ (.inl rfl),onPair _ (.inr rfl)⟩
      · exact ⟨fresh k,prior k,h,onPair _ (.inr rfl),onPair _ (.inl rfl)⟩
    · apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨a,b,ab,ha,hb⟩ := (computes _).mp he
      have only (v : Fin (m+2)) (h : (chain k.val v && pair k v) = true) : v = prior k := by
        simp only [chain,pair,Bool.and_eq_true,decide_eq_true_eq] at h
        rcases h.2 with hp | hp
        · exact hp
        · exact False.elim (by have hv := h.1; rw [hp] at hv; exact (lt_irrefl _) hv)
      rw [only a ha,only b hb] at ab
      exact loopless _ ab
  · intro k v hv
    rcases of_decide_eq_true hv with h | h
    · have hh := smaller k
      subst v
      simp only [chain,decide_eq_true_eq]
      change (prior k).val < k.val+2 at hh
      omega
    · subst v
      simp [chain,fresh]

end Row4201.Charging
#print axioms Row4201.Charging.spanningOrder
