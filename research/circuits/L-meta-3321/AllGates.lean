import WideNet

namespace WideNet

open WideCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- All AND subformulas that fire at x remain true at y. -/
def Stable {n} (x y : Fin n → Bool) (f : Formula n) : Prop :=
  ∀ sub, (Kind.conj,sub) ∈ f.nodes → sub.eval x = true → sub.eval y = true

theorem var_stable {n} (x y : Fin n → Bool) (i : Fin n) : Stable x y (.var i) := by
  simp [Stable,Formula.nodes]

theorem and_stable {n} {x y : Fin n → Bool} (a b : Formula n)
    (ha : Stable x y a) (hb : Stable x y b)
    (value : (a.conj b).eval x = true → (a.conj b).eval y = true) : Stable x y (a.conj b) := by
  intro sub h
  simp only [Formula.conj,Formula.nodes,List.mem_append,List.mem_singleton,Prod.mk.injEq,
    true_and] at h
  rcases h with (h | h) | rfl
  · exact ha _ h
  · exact hb _ h
  · exact value

theorem or_stable {n} {x y : Fin n → Bool} (a b : Formula n)
    (ha : Stable x y a) (hb : Stable x y b) : Stable x y (a.disj b) := by
  intro sub h
  simp [Formula.disj,Formula.nodes] at h
  exact h.elim (ha _) (hb _)

theorem tail_stable {n} (m : ℕ) (P L : Fin (m+1) → Formula n) (x y : Fin n → Bool)
    (Sp : ∀ i, Stable x y (P i)) (Sl : ∀ i, Stable x y (L i))
    (hp : ∀ i, (P i).eval y = false) (hl : ∀ i, (L i).eval y = (L i).eval x)
    (indep : ∀ i, (L i).eval x = true → (P i).eval x = false) : Stable x y (tailF m P L) := by
  induction m with
  | zero => exact Sl 0
  | succ m ih =>
    refine and_stable _ _ (Sl _) (or_stable _ _ (Sp _)
      (ih _ _ (fun i => Sp i.succ) (fun i => Sl i.succ) (fun i => hp i.succ)
        (fun i => hl i.succ) (fun i => indep i.succ))) ?_
    change (tailF (m+1) P L).eval x = true → (tailF (m+1) P L).eval y = true
    rw [eval_tail, eval_tail, WideDefect.tail_on_independent _ _ _ indep,
      WideDefect.tail_on_independent _ _ _ (fun i _ => hp i)]
    exact fun h i => (hl i).trans (h i)

theorem diagonal_stable {n} (m : ℕ) (P L : Fin (m+1) → Formula n) (x y : Fin n → Bool)
    (Sp : ∀ i, Stable x y (P i)) (Sl : ∀ i, Stable x y (L i))
    (indep : ∀ i, (L i).eval x = true → (P i).eval x = false) : Stable x y (diagonalF m P L) := by
  induction m with
  | zero =>
    apply and_stable _ _ (Sp 0) (Sl 0)
    intro hv
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hv
    exact False.elim (Bool.false_ne_true ((indep 0 b).symm.trans a))
  | succ m ih =>
    apply or_stable _ _ _ (ih _ _ (fun i => Sp i.succ) (fun i => Sl i.succ)
      (fun i => indep i.succ))
    apply and_stable _ _ (Sp 0) (Sl 0)
    intro hv
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hv
    exact False.elim (Bool.false_ne_true ((indep 0 b).symm.trans a))

theorem output_stable {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) (x y : Fin n → Bool)
    (Sa : Stable x y a) (Sb : Stable x y b) (Sp : ∀ i, Stable x y (P i)) (Sl : ∀ i, Stable x y (L i))
    (hp : ∀ i, (P i).eval y = false) (hl : ∀ i, (L i).eval y = (L i).eval x)
    (indep : ∀ i, (L i).eval x = true → (P i).eval x = false)
    (off : (dirtyF a b P L).eval x = false) : Stable x y (outputF a b P L) := by
  have sd : Stable x y (dirtyF a b P L) :=
    and_stable a _ Sa (or_stable b _ Sb (tail_stable _ _ _ _ _ Sp Sl hp hl indep)) (by
      change (dirtyF a b P L).eval x = true → _
      rw [off]; intro h; contradiction)
  have guard := and_stable (dirtyF a b P L) b sd Sb (by
    change ((dirtyF a b P L).eval x && b.eval x) = true → _
    rw [off]; intro h; contradiction)
  exact or_stable _ _ guard (diagonal_stable _ _ _ _ _ Sp Sl indep)

def rightOnly {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin ((m+2)+(m+2))) :=
  decide (m+2 ≤ i.val) && x i

theorem clean_at_every_other_weight (m) (x : Fin ((m+2)+(m+2)) → Bool)
    (no : (net m).eval (List.ofFn x) = false)
    (wt : WideDefect.weight (pt x 0) (ln x 0) (fun i => pt x i.succ) (fun i => ln x i.succ) ≠ m+2) :
    ∀ j < (net m).gates.length, (gateAt (net m) j).op = .and →
      ((net m).wires (List.ofFn x)).getD ((m+2)+(m+2)+j) false = true →
      ((net m).wires (List.ofFn (rightOnly x))).getD ((m+2)+(m+2)+j) false = true := by
  let P := fun i : Fin (m+1) => point m i.succ
  let L := fun i : Fin (m+1) => line m i.succ
  have active := net_output m x
  have indep : ∀ i : Fin (m+1), (L i).eval x = true → (P i).eval x = false := by
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hp
    have yes := (matching_iff m x).mpr ⟨i.succ, hp, hi⟩
    exact Bool.false_ne_true (no.symm.trans yes)
  have off : (dirtyF (point m 0) (line m 0) P L).eval x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rw [eval_dirty] at h
    exact wt (WideDefect.defect_weight _ _ _ _ (active ▸ no) h)
  have stable : Stable x (rightOnly x) (full m) := by
    apply output_stable (point m 0) (line m 0) P L
    · apply var_stable
    · apply var_stable
    · intro i; apply var_stable
    · intro i; apply var_stable
    · intro i
      change (decide (m+2 ≤ i.succ.val) && _) = false
      rw [decide_eq_false (Nat.not_le.mpr i.succ.isLt)]; rfl
    · intro i
      change (decide (m+2 ≤ (m+2)+i.succ.val) && _) = _
      rw [decide_eq_true (Nat.le_add_right _ _)]; rfl
    · exact indep
    · exact off
  intro j hj hand fire
  have hj' : j < (full m).nodes.length := circuit_size (full m) ▸ hj
  have gate := circuit_gate (full m) j hj'
  have kind : (full m).nodes[j].1 = Kind.conj := by
    have e := hand.symm.trans gate.1
    cases op : (full m).nodes[j].1 <;> simp [op,Kind.op] at e ⊢
  have mem : (Kind.conj, (full m).nodes[j].2) ∈ (full m).nodes := by
    rw [←kind]
    exact List.getElem_mem _
  have f := (gate.2 x).symm.trans fire
  exact (gate.2 _).trans (stable _ mem f)

def leftOnly {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin ((m+2)+(m+2))) :=
  decide (i.val < m+2) && x i

theorem pt_left {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) : pt (leftOnly x) i = pt x i := by
  change (decide (i.val < m+2) && _) = _
  rw [decide_eq_true i.isLt]; rfl

theorem ln_left {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) : ln (leftOnly x) i = false := by
  change (decide ((m+2) + i.val < m+2) && _) = false
  rw [decide_eq_false (by omega : ¬ ((m+2) + i.val < m+2))]; rfl

theorem pt_right {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) : pt (rightOnly x) i = false := by
  change (decide (m+2 ≤ i.val) && _) = _
  rw [decide_eq_false (Nat.not_le.mpr i.isLt)]; rfl

theorem ln_right {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) : ln (rightOnly x) i = ln x i := by
  change (decide (m+2 ≤ (m+2) + i.val) && _) = _
  rw [decide_eq_true (Nat.le_add_right _ _)]; rfl

/-- The distinguished gate produces a genuine violation of both projection alternatives
at the unique activated independent input. The two wire tests use that same gate index. -/
theorem fails_both_projections (m : ℕ) :
    ∃ j < (net m).gates.length, (gateAt (net m) j).op = .and ∧
      (net m).eval (List.ofFn (badInput m)) = false ∧
      ((net m).wires (List.ofFn (badInput m))).getD ((m+2)+(m+2)+j) false = true ∧
      (∀ x : Fin ((m+2)+(m+2)) → Bool, ((net m).wires (List.ofFn (leftOnly x))).getD ((m+2)+(m+2)+j) false = false ∧
            ((net m).wires (List.ofFn (rightOnly x))).getD ((m+2)+(m+2)+j) false = false) := by
  obtain ⟨j,hj,hk,he⟩ := net_dirty m
  have input :
      (net m).eval (List.ofFn (badInput m)) = false ∧
      ((net m).wires (List.ofFn (badInput m))).getD ((m+2)+(m+2)+j) false = true := by
    rw [net_output, he, WideDefect.unique_obstruction]
    simp only [pt,ln,badInput,Fin.addCases_left,Fin.addCases_right]
    simp
  refine ⟨j,hj,hk,input.1,input.2,fun x => ?_⟩
  simp only [he,pt_left,ln_left,pt_right,ln_right]
  exact WideDefect.pure_projections (pt x 0) (ln x 0) (fun i => pt x i.succ) (fun i => ln x i.succ)

end WideNet
