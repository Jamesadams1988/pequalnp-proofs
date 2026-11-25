import CapacityBudget
import EssentialEdges

/-! Each required edge is an actual source occurrence in the live dependency cone. -/
namespace CliqueSources
open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch
open CPTargetTrace CliqueEdges

private theorem addH {a : Var → Bool} {e f : L} (h : e.Holds a) (h' : f.Holds a) :
    CPLine.Holds a (e.1+f.1,e.2+f.2) := by
  simp only [CPLine.Holds,Pi.add_apply,add_mul,Finset.sum_add_distrib] at *
  omega

private theorem mulH {a : Var → Bool} {e : L} (k : ℕ) (h : e.Holds a) :
    CPLine.Holds a ((k:ℤ) • e.1,(k:ℤ)*e.2) := by
  change (k:ℤ)*e.2 ≤ ∑ v, ((k:ℤ)*e.1 v)*(if a v then 1 else 0)
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem divH {a : Var → Bool} {e : L} (d : ℕ) (h : e.Holds a) (hd : 0 < d)
    (dv : ∀ v, (d:ℤ) ∣ e.1 v) :
    CPLine.Holds a (fun v => e.1 v/(d:ℤ),-((-e.2)/(d:ℤ))) := by
  let t := ∑ v, (e.1 v/(d:ℤ))*(if a v then (1:ℤ) else 0)
  have prod : (d:ℤ)*t = ∑ v, e.1 v*(if a v then 1 else 0) := by
    simp only [t, Finset.mul_sum, ← mul_assoc, Int.mul_ediv_cancel_of_dvd (dv _)]
  change -((-e.2)/(d:ℤ)) ≤ t
  have le := (Int.le_ediv_iff_mul_le (by exact_mod_cast hd : 0 < (d:ℤ))).mpr
    (show (-t)*(d:ℤ) ≤ -e.2 by
      change e.2 ≤ _ at h
      nlinarith only [prod,h])
  omega

theorem coverage {read : ℕ → L} {rule : ℕ → Rule Var} {live : Finset ℕ} {root : ℕ}
    (member : root ∈ live) (target : read root = cap)
    (legal : ∀ i ∈ live, legalRule edges i read (read i) (rule i))
    (closed : closedUnder (fun i => parents (rule i)) live) (k : Fin 6) :
    ∃ i ∈ live, ruleKind (rule i) = .source ∧ read i = clauseCP (pairClause k) := by
  by_contra missing
  have allLines (i : ℕ) : i ∈ live → (read i).Holds (point k) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      have h := legal i hi
      have prior (j : ℕ) (p : j ∈ parents (rule i)) :=
        ih j (parent_lt h j p) (closed i hi j p)
      rcases op : rule i with (C | (v | v)) | (⟨p,q⟩ | (⟨p,d⟩ | ⟨p,d⟩))
      · rw [op] at h
        obtain ⟨⟨j,rfl⟩,eq⟩ := h
        rw [eq]
        refine ((witnesses k).1 j).mpr ?_
        rintro rfl
        exact missing ⟨i,hi,by simp [op,ruleKind],eq⟩
      · rw [op] at h
        exact h ▸ ((witnesses k).2.1 v).1
      · rw [op] at h
        exact h ▸ ((witnesses k).2.1 v).2
      · have hp := prior p (by simp [op, parents])
        have hq := prior q (by simp [op, parents])
        rw [op] at h
        exact h.2.2 ▸ addH hp hq
      · have hp := prior p (by simp [op, parents])
        rw [op] at h
        exact h.2 ▸ mulH d hp
      · have hp := prior p (by simp [op, parents])
        rw [op] at h
        exact h.2.2.2 ▸ divH d hp h.2.1 h.2.2.1
  have hc := allLines root member
  rw [target] at hc
  exact (witnesses k).2.2 hc

end CliqueSources
#print axioms CliqueSources.coverage
