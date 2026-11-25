import ChargeCount
import Separation
import ExtremalVerifier

/-! A monotone chain of accepted inputs can charge a different OR on each step
when a second accepted input has a rejected meet with its predecessor. -/
namespace Row4201.Charging
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PG4Separation

private theorem readMono {n : ℕ} (C : Circuit) (hc : Monotone2 C) (j w : ℕ)
    {x y : Fin n → Bool} (xy : ∀ v, x v = true → y v = true) :
    prefixRead C j x w = true → prefixRead C j y w = true :=
  ExtremalVerifier.evalMono (⟨C.gates.take j,w⟩ : Circuit)
    (fun g h => hc g (List.mem_of_mem_take h)) xy

theorem lowerWithCore {n : ℕ} (C : Circuit) (hc : Monotone2 C) (K : ℕ)
    (chain : ℕ → Fin n → Bool) (witness : Fin K → Fin n → Bool)
    (core : Finset (Fin C.gates.length))
    (coreReady : ∀ j ∈ core, isOr C.gates[j] = true ∧
       ∀ w ∈ C.gates[j].inputs, prefixRead C j (chain 0) w = true)
    (prefixMono : ∀ {i j : ℕ}, i ≤ j → ∀ v, chain i v = true → chain j v = true)
    (samples : ∀ k : Fin K, C.eval (List.ofFn (chain k.val)) = true ∧
      C.eval (List.ofFn (witness k)) = true ∧
      C.eval (List.ofFn (fun v => chain k.val v && witness k v)) = false)
    (witnessNext : ∀ k : Fin K, ∀ v, witness k v = true → chain (k.val+1) v = true) :
    K + core.card ≤ C.gates.countP isOr := by
  let ready (j : Fin C.gates.length) (t : ℕ) : Prop :=
    ∀ w ∈ C.gates[j].inputs, prefixRead C j (chain t) w = true
  apply countWithCore C.gates ready core coreReady
  · intro j a b ab h w hw
    exact readMono C hc j w (prefixMono ab) (h w hw)
  · intro k
    obtain ⟨old,other,meet⟩ := samples k
    obtain ⟨j,g,u,v,hg,op,shape,au,_,av,bv⟩ :=
      separatingOR C hc (chain k.val) (witness k) old other meet
    obtain ⟨hj, agree⟩ := List.getElem?_eq_some_iff.mp hg
    subst g
    refine ⟨⟨j,hj⟩, ?_, ?_, ?_⟩
    · simp [isOr,op]
    · intro wasReady
      have hv : v ∈ C.gates[j].inputs := by rcases shape with h | h <;> simp [h]
      have := wasReady v hv
      exact Bool.noConfusion (av.symm.trans this)
    · intro w hw
      have either : w = u ∨ w = v := by
        rcases shape with h | h <;> simpa [h,or_comm] using hw
      rcases either with rfl | rfl
      · exact readMono C hc j w (prefixMono (Nat.le_succ k.val)) au
      · exact readMono C hc j w (witnessNext k) bv

theorem lower {n : ℕ} (C : Circuit) (hc : Monotone2 C) (K : ℕ)
    (chain : ℕ → Fin n → Bool) (witness : Fin K → Fin n → Bool)
    (prefixMono : ∀ {i j : ℕ}, i ≤ j → ∀ v, chain i v = true → chain j v = true)
    (samples : ∀ k : Fin K, C.eval (List.ofFn (chain k.val)) = true ∧
      C.eval (List.ofFn (witness k)) = true ∧
      C.eval (List.ofFn (fun v => chain k.val v && witness k v)) = false)
    (witnessNext : ∀ k : Fin K, ∀ v, witness k v = true → chain (k.val+1) v = true) :
    K ≤ C.gates.countP isOr := by
  simpa using lowerWithCore C hc K chain witness ∅ (by simp) prefixMono samples witnessNext

end Row4201.Charging
#print axioms Row4201.Charging.lowerWithCore
#print axioms Row4201.Charging.lower
