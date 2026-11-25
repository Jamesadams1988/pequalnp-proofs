import PEqualNP.Defs

namespace IncidenceComparison
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Assigned : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + j) false = true → (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)

def PointLineNormal : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)

private theorem apart {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at this
  have := p.isLt
  omega

theorem implies_3451 (h : Assigned) : PointLineNormal := by
  intro N I dec C h4 hm hb he
  obtain ⟨D,md,bd,sd,ed,clean,hot⟩ := h N I C h4 hm hb he
  refine ⟨D,md,bd,sd,ed,?_,hot⟩
  intro j hj hand p l hn
  let pair : Fin (N+N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  have repr : l.addNat N = Fin.natAdd N l := Fin.ext (Nat.add_comm l.val N)
  have lp : (fun k : Fin (N+N) => decide (k.val < N) && pair k) = (fun k => decide (k = Fin.castAdd N p)) := by
    funext k
    by_cases a : k = Fin.castAdd N p
    · subst k; simp [pair,p.isLt]
    by_cases b : k = Fin.natAdd N l
    · subst k; simp [pair]; simpa only [repr] using (apart p l).symm
    simp [pair,a]; grind [Fin.val_addNat, Fin.val_natAdd]
  have rp : (fun k : Fin (N+N) => decide (N ≤ k.val) && pair k) = (fun k => decide (k = Fin.natAdd N l)) := by
    funext k
    by_cases b : k = Fin.natAdd N l
    · subst k; simp [pair]
    by_cases a : k = Fin.castAdd N p
    · subst k; simp [pair,Nat.not_le_of_lt p.isLt]; simpa only [repr] using apart p l
    simp [pair,a]; grind [Fin.val_addNat, Fin.val_natAdd]
  apply Bool.eq_false_iff.mpr
  intro live
  have one := hot j hj hand
  rcases clean j hj hand pair live with left | right | ⟨q,k,inc,pp,ll⟩
  · rw [lp,one.1 p] at left; contradiction
  · rw [rp,one.2 l] at right; contradiction
  · simp only [pair,decide_eq_true_eq] at pp ll
    obtain a | a := pp
    · have e : q = p := Fin.ext (congrArg (fun z : Fin (N+N) => z.val) a)
      subst q
      obtain b | b := ll
      · exact apart p k b.symm
      · have e : k = l := by
          apply Fin.ext; have t := congrArg Fin.val b
          simp only [Fin.val_natAdd] at t; omega
        exact hn (e ▸ inc)
    · exact apart q l a

end IncidenceComparison
