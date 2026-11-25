import Structure

namespace Split12578.Bridge

theorem exact_opposite : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) :=
  fun claim => claim positive

#print axioms exact_opposite

end Split12578.Bridge
