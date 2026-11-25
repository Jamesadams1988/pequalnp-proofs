import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_9526

/-! On the face where input 0 is false and input 5 is true, this table
detects the edges of the complete graph on inputs 1, 2, 3 and 4.
Each essential restriction costs a gate by the elimination lemma from
nicohabets's L-meta-4795, crediting sanchan. The seven-gate lower bound
for the four-clique is hilelyos's L-meta-9526. -/

namespace L13194Exact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (one_gate_at relabel_size)
open PEqualNP.Outside.L_meta_9526 (targetK4 lb_K4)

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4294901482 * 2 ^ 32 + 4278124266)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

/-- Apart from singleton 0, the minimal terms are 12, the cross pairs
13, 14, 23, 24, and the triple 345. -/
def monoWitness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 2]⟩,
     ⟨.and, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [5, 9]⟩,
     ⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩

theorem witness_ops :
    ∀ g ∈ monoWitness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [monoWitness]

theorem witness_size : monoWitness.size = 9 := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, monoWitness.eval (List.ofFn x) = target x := by
  decide +kernel

private def core (x : Fin 6 → Bool) := target (Function.update x 0 false)
private def clique (x : Fin 6 → Bool) := core (Function.update x 5 true)

private theorem singletonEssential : ∃ x, target (Function.update x 0 (!x 0)) ≠ target x :=
  ⟨fun _ => false, by decide +kernel⟩

private def pair12 (i : Fin 6) := decide (i = 1 ∨ i = 2)
private def pair34 (i : Fin 6) := decide (i = 3 ∨ i = 4)

private theorem coreNonconstant : ∃ x y, core x ≠ core y :=
  ⟨fun _ => false, pair12, by decide +kernel⟩

private theorem lastEssential : ∃ x, core (Function.update x 5 (!x 5)) ≠ core x :=
  ⟨pair34, by decide +kernel⟩

private theorem cliqueNonconstant : ∃ x y, clique x ≠ clique y :=
  ⟨fun _ => false, pair12, by decide +kernel⟩

private def label : Fin 6 → Fin 4 := ![0, 0, 1, 2, 3, 0]

private theorem cliqueEq : (fun x : Fin 4 → Bool => clique (x ∘ label)) = targetK4 := by
  funext x
  revert x
  decide +kernel

section Restrictions

attribute [local irreducible] target

theorem lower {s : ℕ} (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  obtain ⟨t, ht, hcore⟩ : ∃ t, t+1 ≤ s ∧ HasCircuitSize 6 core t :=
    one_gate_at 5 target 0 false s singletonEssential coreNonconstant h
  obtain ⟨u, hu, hclique⟩ : ∃ u, u+1 ≤ t ∧ HasCircuitSize 6 clique u :=
    one_gate_at 5 core 5 true t lastEssential cliqueNonconstant hcore
  have hc : HasCircuitSize 4 (fun x => clique (x ∘ label)) u :=
    relabel_size label clique u hclique
  have hk := lb_K4 u (cliqueEq ▸ hc)
  omega

end Restrictions

theorem exactMinimum :
    HasCircuitSize 6 target 9 ∧ (∀ s, HasCircuitSize 6 target s → 9 ≤ s) ∧
    Monotone2 monoWitness ∧ monoWitness.size = 9 ∧
    ∀ x : Fin 6 → Bool, monoWitness.eval (List.ofFn x) = target x := by
  have legal : FanInTwo monoWitness := by
    intro g hg
    obtain ⟨hop, har⟩ := witness_ops g hg
    exact ⟨hop.elim Or.inl (fun h => Or.inr (Or.inl h)), har⟩
  exact ⟨⟨monoWitness, legal, le_rfl, witness_eval⟩,
    fun _ h => lower h, witness_ops, witness_size, witness_eval⟩

theorem assignedStatementFalse : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4278124266) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4278124266) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro claimed
  apply claimed
  intro s h
  exact ⟨monoWitness, witness_ops, lower h, witness_eval⟩

end L13194Exact

#print axioms L13194Exact.exactMinimum
#print axioms L13194Exact.assignedStatementFalse
