import Transfer

namespace FirstFive.Cofactor3
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev target := FirstFive.Cofactor.target

def donor := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7))

def rename : Fin 9 → Fin 9 := ![3,1,7,8,5,0,6,4,2]

def permTarget (x : Fin 9 → Bool) := target (x ∘ rename)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cofactor : ∀ x : Fin 8 → Bool, permTarget (Fin.snoc x false) = donor x := by decide

theorem last_dep : ∃ x, permTarget (Function.update x (Fin.last 8) (!x (Fin.last 8))) ≠ permTarget x := by
  refine ⟨fun i => decide (i=2), ?_⟩
  decide

theorem remaining_nonconstant : ∃ x y, permTarget (Fin.snoc x false) ≠ permTarget (Fin.snoc y false) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

theorem unrestricted_lower
    (checked : ∀ t : ℕ, HasCircuitSize 8 donor t → 14 ≤ t)
    (t : ℕ) (h : HasCircuitSize 9 target t) : 15 ≤ t := by
  by_contra! ht
  obtain ⟨C, fan, size, eq⟩ := h
  have h14 : HasCircuitSize 9 target 14 := ⟨C,fan,by omega,eq⟩
  have permuted : HasCircuitSize 9 permTarget 14 := relabel_size rename target 14 h14
  have residual := gate_elim 8 permTarget false 13 last_dep remaining_nonconstant permuted
  rw [funext cofactor] at residual
  have := checked 13 residual
  omega

theorem first_wire_lower (checked : ∀ t : ℕ, HasCircuitSize 8 donor t → 14 ≤ t)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : FanInTwo C)
    (value : circuitFun 9 C = target) : 15 ≤ C.size :=
  unrestricted_lower checked C.size ⟨C,fan,le_rfl,congrFun value⟩

#print axioms unrestricted_lower
end FirstFive.Cofactor3
