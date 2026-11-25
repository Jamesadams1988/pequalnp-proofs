import PEqualNP.Outside.L_meta_13081

/-!
The table of L-meta-13081 is the De Morgan dual of the table of L-meta-15250
after relabeling inputs. The eight-gate circuit below swaps AND and OR in the
L-meta-15250 witness and relabels its input wires. The unrestricted lower bound
comes from MiguelTorresPerez's merged L-meta-13081 (PR #17264). Nico Habets
also gave a matching eight-gate witness and lower bound in PR #18534.
The identity below records how the two six-input tables are related.
-/
namespace Row13081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_13081 (F0 lb_size root)

def row15250 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3936927872 * 2 ^ 32 + 3934830720)
    (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)

def inputLabel : Fin 6 → Fin 6 := ![0, 1, 3, 4, 2, 5]

set_option maxRecDepth 8192 in
theorem dualTable : ∀ x, F0 x = !(row15250 (fun i => !x (inputLabel i))) := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [3, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩,
    ⟨.and, [4, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩

set_option maxRecDepth 8192 in
theorem witness_correct : Monotone2 witness ∧ witness.size = 8 ∧
    ∀ x, witness.eval (List.ofFn x) = F0 x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [witness, Monotone2]
  · decide +kernel

theorem exactMinimum : HasCircuitSize 6 F0 8 ∧ (∀ s, HasCircuitSize 6 F0 s → 8 ≤ s) := by
  obtain ⟨hm, hs, he⟩ := witness_correct
  refine ⟨⟨witness, ?_, hs.le, he⟩, lb_size F0 8 root⟩
  intro g hg
  obtain ⟨op, fanin⟩ := hm g hg
  exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), fanin⟩

#print axioms Row13081.exactMinimum
end Row13081
