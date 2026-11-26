import Lower
import PEqualNP.Outside.L_meta_1500
import PEqualNP.Outside.L_meta_4580

namespace Plane1988
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4580 (permCircuit permCircuit_eval permCircuit_mono permCircuit_size permCircuit_lineDeg)

/-- Relabel the lines by negation to pass from sum to difference coordinates.
The other choice first exchanges points and lines. -/
def reindex (swap : Bool) (i : Fin 26) : Fin 26 :=
  let k := Fin.ofNat 13 i.val
  if (i.val < 13) = (swap = false) then Fin.castAdd 13 k else Fin.natAdd 13 (-k)

def difference (p w : Fin 13) : Prop :=
  ∃ d : ℕ, d ∈ ({0,1,3,9} : Finset ℕ) ∧ (w.val + d) % 13 = p.val

private def hit (p w : Fin 13) : Prop :=
  (w.val + 0) % 13 = p.val ∨ (w.val + 1) % 13 = p.val ∨
  (w.val + 3) % 13 = p.val ∨ (w.val + 9) % 13 = p.val

private instance : DecidableRel hit := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem hit_iff (p w : Fin 13) : hit p w ↔ difference p w := by
  simp only [hit,difference,Finset.mem_insert,Finset.mem_singleton]
  grind

private def places (s : Bool) (e : Fin 26 × Fin 26) (p w : Fin 13) : Prop :=
  (reindex s e.1 = Fin.castAdd 13 p ∧ reindex s e.2 = Fin.natAdd 13 w) ∨
  (reindex s e.2 = Fin.castAdd 13 p ∧ reindex s e.1 = Fin.natAdd 13 w)

private instance (s e p w) : Decidable (places s e p w) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

set_option maxRecDepth 8192 in
private theorem forward : ∀ s : Bool, ∀ e ∈ Elimination.edges, ∃ p w, hit p w ∧ places s e p w := by decide +kernel

set_option maxRecDepth 8192 in
private theorem reverse : ∀ s : Bool, ∀ p w, hit p w → ∃ e ∈ Elimination.edges, places s e p w := by decide +kernel

private theorem mapped (s : Bool) (x : Fin 26 → Bool) :
    Elimination.target (fun i => x (reindex s i)) = true ↔
    ∃ p w, difference p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true := by
  constructor
  · intro h
    obtain ⟨e,he,bits⟩ := List.any_eq_true.mp h
    obtain ⟨p,w,hi,hpl⟩ := forward s e he
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp bits
    refine ⟨p,w,(hit_iff _ _).mp hi,?_⟩
    rcases hpl with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ ha,h2 ▸ hb⟩
    · exact ⟨h1 ▸ hb,h2 ▸ ha⟩
  · rintro ⟨p,w,hi,hp,hw⟩
    obtain ⟨e,he,ord⟩ := reverse s p w ((hit_iff _ _).mpr hi)
    apply List.any_eq_true.mpr
    refine ⟨e,he,Bool.and_eq_true_iff.mpr ?_⟩
    change x (reindex s e.1) = true ∧ x (reindex s e.2) = true
    rcases ord with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1.symm ▸ hp,h2.symm ▸ hw⟩
    · exact ⟨h2.symm ▸ hw,h1.symm ▸ hp⟩

private def shore (s : Bool) : Finset ℕ :=
  if s then Finset.range 13 else Finset.Ico 13 26

private theorem marked : ∀ s : Bool, ∀ i : Fin 26,
    (reindex s i).val ∈ Finset.Ico 13 26 ↔ i.val ∈ shore s := by decide +kernel

theorem degreeOnShore {C : Circuit} {outs : List ℕ} (hm : Monotone2 C) (hlen : outs.length ≤ 2)
    (ht : Tests C outs) (hs : C.size ≤ 62) (s : Bool) :
    2 ≤ (appendAnd C outs).lineDeg 26 (shore s) := by
  let A := appendAnd C outs
  let K := permCircuit (reindex s) A
  have correct (x : Fin 26 → Bool) : circuitFun 26 K x = true ↔
      ∃ p w, difference p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true := by
    rw [show circuitFun 26 K x = circuitFun 26 A (fun i => x (reindex s i)) from permCircuit_eval ..]
    rw [show circuitFun 26 A = Elimination.target from computes hm ht]
    exact mapped s x
  by_contra! hdeg
  apply PEqualNP.Outside.L_meta_1500
  refine ⟨K,permCircuit_mono _ _ (mono_append hm hlen),?_,?_,?_,?_⟩
  · change (permCircuit _ (appendAnd C outs)).size ≤ 63
    rw [permCircuit_size,size_append]
    omega
  · change (permCircuit (reindex s) A).lineDeg 26 (Finset.Ico 13 26) ≤ 1
    rw [permCircuit_lineDeg _ _ _ _ (marked s)]
    exact Nat.le_of_lt_succ hdeg
  · intro x _ hx
    exact (correct x).mp hx
  · intro p w hi
    apply (correct _).mpr
    exact ⟨p,w,hi,by simp,by simp⟩

theorem bothDegrees {C : Circuit} {outs : List ℕ} (hm : Monotone2 C) (hlen : outs.length ≤ 2)
    (ht : Tests C outs) (hs : C.size ≤ 62) :
    2 ≤ (appendAnd C outs).lineDeg 26 (Finset.range 13) ∧
    2 ≤ (appendAnd C outs).lineDeg 26 (Finset.Ico 13 26) :=
  ⟨degreeOnShore hm hlen ht hs true,degreeOnShore hm hlen ht hs false⟩

end Plane1988
#print axioms Plane1988.bothDegrees
