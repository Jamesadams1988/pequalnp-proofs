import CapacityBudget
import EssentialEdges
import RankOne

/-! Two distinct official division occurrences are necessary in the live
trace of the K4 column capacity. Pair and Boolean axioms, parallel
multiplication, sharing, and both operands of an addition are allowed. -/
namespace CliqueDivisions
open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch
open CPTargetTrace CliqueEdges CliqueCut

def upper (e : L) : Upper 4 := ⟨fun v => -e.1 v, -e.2⟩

private theorem upperExt (a b : Upper 4) (coef : ∀ v, a.coeff v = b.coeff v)
    (rhs : a.rhs = b.rhs) : a = b := by
  cases a; cases b; congr 1; exact funext coef

private theorem edgeRaw (C : Clause Var) (hC : C ∈ edges) : Raw 4 (upper (clauseCP C)) := by
  obtain ⟨k,rfl⟩ := hC
  have shape : ∀ k : Fin 6, ∀ v : Var,
      (upper (clauseCP (pairClause k))).coeff v =
      unit (ends k).1 v + unit (ends k).2 v := by decide +kernel
  have rhs : ∀ k : Fin 6, (upper (clauseCP (pairClause k))).rhs = 1 := by decide +kernel
  have ne : ∀ k : Fin 6, (ends k).1 ≠ (ends k).2 := by decide +kernel
  rw [upperExt _ ⟨fun v => unit (ends k).1 v + unit (ends k).2 v, 1⟩ (shape k) (rhs k)]
  exact Raw.pair _ _ (ne k)

private theorem loRaw (i : Var) : Raw 4 (upper (lo i)) := by
  rw [upperExt (upper (lo i)) ⟨fun v => -unit i v, 0⟩ (fun _ => rfl) (by change -(0:ℤ) = 0; decide)]
  exact Raw.lo i

private theorem hiRaw (i : Var) : Raw 4 (upper (hi i)) := by
  have c : ∀ i v : Var, (upper (hi i)).coeff v = unit i v := by decide +kernel
  rw [upperExt _ ⟨unit i, 1⟩ (c i) (by change -(-1:ℤ) = 1; decide)]
  exact Raw.hi i

private theorem plusUpper (a b : L) :
    upper (a.1+b.1, a.2+b.2) = CliqueCut.add (upper a) (upper b) := by
  apply upperExt <;> simp [upper, CliqueCut.add, add_comm]

private theorem timesUpper (k : ℕ) (a : L) :
    upper ((k:ℤ) • a.1, (k:ℤ)*a.2) = scale k (upper a) := by
  apply upperExt <;> simp [upper,scale]

private theorem divided {e : L} (d : ℕ) (pos : 0 < d) (dvd : ∀ v, (d:ℤ) ∣ e.1 v)
    (before : Raw 4 (upper e)) :
    RankOne 4 (upper (fun v => e.1 v/(d:ℤ), -((-e.2)/(d:ℤ)))) := by
  let a := fun v => -(e.1 v/(d:ℤ))
  have shape : upper e = ⟨fun v => (d:ℤ)*a v,-e.2⟩ := by
    apply upperExt
    · intro v; simp [upper,a,Int.mul_ediv_cancel_of_dvd (dvd v)]
    · rfl
  have cut := RankOne.cut a (-e.2) (d:ℤ) (by omega) (shape ▸ before)
  simpa [upper,a] using cut

/-- The bound concerns the actual selected live occurrences, without counting
any divisions outside the root's dependency trace. -/
theorem atLeastTwo {read : ℕ → L} {rule : ℕ → Rule Var} {live : Finset ℕ} {root : ℕ}
    (member : root ∈ live) (target : read root = cap)
    (legal : ∀ i ∈ live, legalRule edges i read (read i) (rule i))
    (closed : closedUnder (fun i => parents (rule i)) live) :
    2 ≤ countKind live rule .division := by
  by_contra! small
  have count : (live.filter (fun i => ruleKind (rule i) = .division)).card ≤ 1 := by
    change countKind live rule .division ≤ 1
    omega
  have unique (i j : ℕ) (hi : i ∈ live) (hj : j ∈ live)
      (di : ruleKind (rule i) = .division) (dj : ruleKind (rule j) = .division) : i = j :=
    Finset.card_le_one.mp count _ (Finset.mem_filter.mpr ⟨hi,di⟩) _ (Finset.mem_filter.mpr ⟨hj,dj⟩)
  let uncut (i : ℕ) := ∀ j ∈ live, j ≤ i → ruleKind (rule j) ≠ .division
  have allLines (i : ℕ) : i ∈ live → RankOne 4 (upper (read i)) ∧
      (uncut i → Raw 4 (upper (read i))) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      have h := legal i hi
      have prior (j : ℕ) (p : j ∈ parents (rule i)) :=
        ih j (parent_lt h j p) (closed i hi j p)
      have down {p : ℕ} (hp : p < i) (u : uncut i) : uncut p :=
        fun j hj le => u j hj (Nat.le_trans le hp.le)
      have source (hr : Raw 4 (upper (read i))) := And.intro (RankOne.raw hr) (fun _ : uncut i => hr)
      rcases op : rule i with (C | (v | v)) | (⟨p,q⟩ | (⟨p,k⟩ | ⟨p,d⟩))
      · rw [op] at h
        exact source (h.2 ▸ edgeRaw C h.1)
      · rw [op] at h
        exact source (h ▸ loRaw v)
      · rw [op] at h
        exact source (h ▸ hiRaw v)
      · have pa := prior p (by simp [op,parents])
        have qa := prior q (by simp [op,parents])
        rw [op] at h
        obtain ⟨hp,hq,eq⟩ := h
        rw [eq,plusUpper]
        exact ⟨RankOne.plus pa.1 qa.1, fun u => Raw.plus (pa.2 (down hp u)) (qa.2 (down hq u))⟩
      · have pa := prior p (by simp [op,parents])
        rw [op] at h
        obtain ⟨hp,eq⟩ := h
        rw [eq,timesUpper]
        exact ⟨RankOne.times _ pa.1, fun u => Raw.times _ (pa.2 (down hp u))⟩
      · have pa := prior p (by simp [op,parents])
        have di : ruleKind (rule i) = .division := by simp [op,ruleKind]
        rw [op] at h
        obtain ⟨hp,hd,hv,eq⟩ := h
        have before : uncut p := by
          intro j hj le dj
          have same := unique j i hj hi dj di
          omega
        rw [eq]
        exact ⟨divided d hd hv (pa.2 before), fun u => (u i hi (Nat.le_refl i) di).elim⟩
  have rank := (allLines root member).1
  rw [target] at rank
  exact cliqueFourNeedsTwoRounds (by simpa [upper,cap] using rank)

end CliqueDivisions
#print axioms CliqueDivisions.atLeastTwo
