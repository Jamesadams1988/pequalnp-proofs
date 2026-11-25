import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_8650

/-!
The witness extends the five-input factorization in L-meta-8650 by gating its
second input-2 occurrence with input 5. The converse pins input 5 high and
uses L-meta-8650's unrestricted lower bound. The elimination and relabeling
lemmas from Nico Habets's L-meta-4795 derive from sanchan's L-meta-927.
The five-input checker credits ljste, jfsantoropereira and L-meta-1421.
-/

namespace Row15250
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (one_gate_at relabel_size)

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3936927872 * 2 ^ 32 + 3934830720)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩,
    ⟨.and, [2, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [0, 10]⟩,
    ⟨.or, [3, 11]⟩, ⟨.and, [8, 12]⟩], 13⟩

set_option maxRecDepth 8192 in
theorem witness_correct : Monotone2 witness ∧ witness.size = 8 ∧
    ∀ x, witness.eval (List.ofFn x) = target x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [witness, Monotone2]
  · decide +kernel

def label : Fin 6 → Fin 5 := ![0, 1, 2, 3, 4, 0]

set_option maxRecDepth 8192 in
theorem image : ∀ y, target (Function.update (y ∘ label) 5 true) =
    PEqualNP.Outside.L_meta_8650_aux.targetFunction y := by decide +kernel

theorem lower (s : ℕ) (h : HasCircuitSize 6 target s) : 8 ≤ s := by
  have essential : ∃ x, target (Function.update x 5 (!x 5)) ≠ target x :=
    ⟨fun i => (21 : ℕ).testBit i, by decide +kernel⟩
  have nc : ∃ x y, target (Function.update x 5 true) ≠ target (Function.update y 5 true) :=
    ⟨fun _ => false, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  obtain ⟨t, ht, hface⟩ := one_gate_at 5 target 5 true s essential nc h
  have hg := relabel_size label _ t hface
  change HasCircuitSize 5 (fun y => target (Function.update (y ∘ label) 5 true)) t at hg
  rw [funext image] at hg
  obtain ⟨C, hf, hs, he⟩ := hg
  have h7 := (PEqualNP.Outside.L_meta_8650_aux.lower C hf he).trans hs
  omega

theorem exactMinimum : HasCircuitSize 6 target 8 ∧
    (∀ s, HasCircuitSize 6 target s → 8 ≤ s) ∧
    Monotone2 witness ∧ witness.size = 8 ∧ ∀ x, witness.eval (List.ofFn x) = target x := by
  obtain ⟨hm, hs, he⟩ := witness_correct
  have hfan : FanInTwo witness := by
    intro g hg
    obtain ⟨op, arity⟩ := hm g hg
    exact ⟨op.elim Or.inl (fun ho => Or.inr (Or.inl ho)), arity⟩
  exact ⟨⟨witness, hfan, hs.le, he⟩, lower, hm, hs, he⟩

theorem assignedStatementFalse : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927872 * 2 ^ 32 + 3934830720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927872 * 2 ^ 32 + 3934830720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro claim
  apply claim
  intro s h
  obtain ⟨hm, hs, he⟩ := witness_correct
  exact ⟨witness, hm, hs.le.trans (lower s h), he⟩

end Row15250

#print axioms Row15250.exactMinimum
#print axioms Row15250.assignedStatementFalse
