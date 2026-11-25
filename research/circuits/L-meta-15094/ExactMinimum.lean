import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_8637

/-!
Input zero factors out as AND. Its true face is exactly the five-input
function in L-meta-8637, without reordering the remaining inputs.
The lower bound uses that row's checked eight-gate lower bound and the
gate elimination and relabeling lemmas of L-meta-4795 (from L-meta-927).
-/

namespace Row15094
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (one_gate_at relabel_size)
open PEqualNP.Outside.L_meta_8637 (Lower fullMask hcsLowerEq hcsLower s0Stock)

def f (x : Fin 6 → Bool) := Nat.testBit (2826995840 * 2^32 + 2290089984)
  (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)
def g (x : Fin 5 → Bool) := Nat.testBit 0xe8a8a800
  (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)

set_option maxRecDepth 8192 in
theorem factor : ∀ x, f x = (x 0 && g (fun i => x i.succ)) := by decide +kernel

/-- The final step of L-meta-8637 turns its checked word certificate into an
unrestricted gate lower bound. -/
theorem coreLower (s : ℕ) (h : HasCircuitSize 5 g s) : 8 ≤ s := by
  let raw : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
  let goal : BitVec 32 := 0xe8a8a800
  have root : Lower (fullMask 32) (raw.map BitVec.toNat) goal.toNat 8 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s0Stock
  exact hcsLower (n := 5) raw goal 8 g (by decide +kernel) (by decide +kernel) root s h

def label : Fin 6 → Fin 5 := ![0, 0, 1, 2, 3, 4]

set_option maxRecDepth 8192 in
theorem image : ∀ y, f (Function.update (y ∘ label) 0 true) = g y := by decide +kernel

theorem lower (s : ℕ) (h : HasCircuitSize 6 f s) : 9 ≤ s := by
  have essential : ∃ x, f (Function.update x 0 (!x 0)) ≠ f x :=
    ⟨fun i => (22 : ℕ).testBit i, by decide +kernel⟩
  have nc : ∃ x y, f (Function.update x 0 true) ≠ f (Function.update y 0 true) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t, ht, pinned⟩ := one_gate_at 5 f 0 true s essential nc h
  have hg := relabel_size label _ t pinned
  change HasCircuitSize 5 (fun y => f (Function.update (y ∘ label) 0 true)) t at hg
  rw [funext image] at hg
  exact (Nat.succ_le_succ (coreLower t hg)).trans ht

/-- Evaluate (x2 OR x3)(x4 OR x5)x1 and x2 x3 x4 x5, take their OR,
then require x0. This is the minterm factorization of the posted table. -/
def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 8]⟩,
    ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [10, 11]⟩,
    ⟨.or, [9, 12]⟩, ⟨.and, [0, 13]⟩], 14⟩

set_option maxRecDepth 8192 in
theorem witness_correct : Monotone2 witness ∧ witness.size = 9 ∧
    ∀ x, witness.eval (List.ofFn x) = f x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [Monotone2, witness]
  · decide +kernel

theorem exactMinimum : HasCircuitSize 6 f 9 ∧ (∀ s, HasCircuitSize 6 f s → 9 ≤ s) ∧
    Monotone2 witness ∧ witness.size = 9 ∧ ∀ x, witness.eval (List.ofFn x) = f x := by
  obtain ⟨hm, hs, he⟩ := witness_correct
  have hfan : FanInTwo witness := by
    intro gate hg
    obtain ⟨op, ar⟩ := hm gate hg
    exact ⟨op.elim Or.inl (fun ho => Or.inr (Or.inl ho)), ar⟩
  exact ⟨⟨witness,hfan,hs.le,he⟩,lower,hm,hs,he⟩

theorem assignedStatementFalse : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2826995840 * 2 ^ 32 + 2290089984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2826995840 * 2 ^ 32 + 2290089984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro claim
  apply claim
  intro s h
  obtain ⟨hm, hs, he⟩ := witness_correct
  exact ⟨witness, hm, hs.le.trans (lower s h), he⟩

end Row15094
#print axioms Row15094.exactMinimum
#print axioms Row15094.assignedStatementFalse
