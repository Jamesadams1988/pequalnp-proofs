import Nine
import DualBudgets

/-! The merged L-meta-13131 proof supplied nine monotone gates. Its exact
unrestricted minimum follows from the L-meta-15174 lower bound by duality and
permutation. The witness here is the dual of the nine-gate formula in Nine.lean. -/

namespace Row15174Dual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [8, 12]⟩,
    ⟨.or, [7, 13]⟩], 14⟩

set_option maxRecDepth 8192 in
theorem exactMinimum13131 : HasCircuitSize 6 g 9 ∧
    (∀ s, HasCircuitSize 6 g s → 9 ≤ s) ∧
    Monotone2 witness ∧ witness.size = 9 ∧ ∀ y, witness.eval (List.ofFn y) = g y := by
  have hm : Monotone2 witness := by simp [Monotone2, witness]
  have hf : FanInTwo witness := by
    intro gate hgate
    obtain ⟨hop, ar⟩ := hm gate hgate
    exact ⟨hop.elim Or.inl (fun ho => Or.inr (Or.inl ho)), ar⟩
  have he : ∀ y, witness.eval (List.ofFn y) = g y := by decide +kernel
  refine ⟨⟨witness, hf, by decide, he⟩, ?_, hm, rfl, he⟩
  intro s hs
  exact PEqualNP.Outside.Row15174Review.exactMinimum.1 s ((budgets s).mpr hs)

end Row15174Dual

#print axioms Row15174Dual.exactMinimum13131
