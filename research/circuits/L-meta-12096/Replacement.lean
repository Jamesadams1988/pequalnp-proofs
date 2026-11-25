import ThresholdCircuit

namespace Row12096

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Count only AND/OR gates with exactly two incoming wires. -/
def binaryGate : Gate → Bool
  | ⟨.and, [_, _]⟩ | ⟨.or, [_, _]⟩ => true
  | _ => false

/-- If a circuit with a NOT requires at least k two-input gates, an available
monotone witness of size at most k+1 fits every budget that computes f. -/
theorem replacementOfBinaryLower {n k : ℕ} {f : (Fin n → Bool) → Bool}
    {w : Circuit} (mono : Monotone2 w) (size : w.size ≤ k + 1)
    (computes : ∀ x, w.eval (List.ofFn x) = f x)
    (lower : ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        (∃ g ∈ C.gates, g.op = .not) → k ≤ C.gates.countP binaryGate) :
    ∀ s, HasCircuitSize n f s →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x, D.eval (List.ofFn x) = f x := by
  rintro s ⟨C, fan, budget, eval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, member, op⟩ := hasNot
    have smaller : C.gates.countP binaryGate < C.size := by
      apply List.countP_lt_length_iff.mpr
      refine ⟨g, member, ?_⟩
      obtain ⟨o, inputs⟩ := g
      change o = .not at op
      subst o
      rfl
    have count := lower C fan eval ⟨g, member, op⟩
    exact ⟨w, mono, by omega, computes⟩
  · refine ⟨C, ?_, budget, eval⟩
    intro g member
    obtain ⟨ops, arity⟩ := fan g member
    refine ⟨?_, arity⟩
    rcases ops with a | b | neg
    · exact Or.inl a
    · exact Or.inr b
    · exact False.elim (hasNot ⟨g, member, neg⟩)

/-- The six-input replacement claim follows from a twelve-binary-gate lower
bound on NOT-using circuits for the same truth table. -/
theorem row12096_of_binaryLower
    (lower : ∀ C : Circuit, FanInTwo C →
      (∀ x, C.eval (List.ofFn x) = ThresholdCircuit.target x) →
      (∃ g ∈ C.gates, g.op = .not) → 12 ≤ C.gates.countP binaryGate) :
    ∀ s, HasCircuitSize 6 ThresholdCircuit.target s →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧
        ∀ x, D.eval (List.ofFn x) = ThresholdCircuit.target x := by
  obtain ⟨hm, hs, he⟩ := ThresholdCircuit.upper
  exact replacementOfBinaryLower hm hs.le he lower

end Row12096

#print axioms Row12096.row12096_of_binaryLower
