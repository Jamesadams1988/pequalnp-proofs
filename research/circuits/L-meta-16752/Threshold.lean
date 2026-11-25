import PEqualNP.Outside.L_meta_12184

/-! The two pins below reduce the posted function to three-of-four.
L-meta-12184 gives the size-preserving dualization, the two-of-four lower
bound and gate elimination used here. Its header credits the source rows. -/
namespace Row16752Review
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12184
open Transfer (one_gate_at relabel_size dual_size)

def full (x : Fin 6 → Bool) := Nat.testBit (4276809450 * 2^32 + 4276808362)
  (∑ i : Fin 6, if x i then 2^(i : Nat) else 0)

def five (x : Fin 5 → Bool) := Nat.testBit 0xe8a8e880
  (∑ i : Fin 5, if x i then 2^(i : Nat) else 0)

def three (x : Fin 4 → Bool) := Nat.testBit 0xe880
  (∑ i : Fin 4, if x i then 2^(i : Nat) else 0)

theorem fiveLower (s : Nat) (h : HasCircuitSize 5 five s) : 8 ≤ s := by
  have dep : ∃ x, five (Function.update x 4 (!x 4)) ≠ five x :=
    ⟨fun i => (3 : Nat).testBit i, by decide +kernel⟩
  have nc : ∃ x y, five (Function.update x 4 false) ≠ five (Function.update y 4 false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t, ht, pinned⟩ := one_gate_at 4 five 4 false s dep nc h
  let label : Fin 5 → Fin 4 := ![0,1,2,3,0]
  have projected := relabel_size label (fun x => five (Function.update x 4 false)) t pinned
  have image : (fun y => five (Function.update (y ∘ label) 4 false)) = three :=
    funext (by decide +kernel)
  rw [image] at projected
  have dual := dual_size three ⟨fun _ => true, by decide +kernel⟩ t projected
  have identity : (fun x : Fin 4 → Bool => !(three (fun i => !x i))) = Transfer.small :=
    funext (by decide +kernel)
  rw [identity] at dual
  have bound := Foundation.lower t dual
  omega

theorem fullLower (s : Nat) (h : HasCircuitSize 6 full s) : 9 ≤ s := by
  have dep : ∃ x, full (Function.update x 0 (!x 0)) ≠ full x :=
    ⟨fun _ => false, by decide +kernel⟩
  have nc : ∃ x y, full (Function.update x 0 false) ≠ full (Function.update y 0 false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t, ht, pinned⟩ := one_gate_at 5 full 0 false s dep nc h
  let label : Fin 6 → Fin 5 := ![0,0,1,2,3,4]
  have projected := relabel_size label (fun x => full (Function.update x 0 false)) t pinned
  have image : (fun y => full (Function.update (y ∘ label) 0 false)) = five :=
    funext (by decide +kernel)
  rw [image] at projected
  have bound := fiveLower t projected
  omega

/-- The five-input factorization appears as gates_e8a8e880 in L-meta-1423.
Shift its input indices by one and append disjunction with the new input. -/
def witness : Circuit :=
  ⟨[⟨.or,[1,4]⟩, ⟨.and,[2,3]⟩, ⟨.or,[2,3]⟩, ⟨.or,[4,5]⟩,
    ⟨.and,[8,9]⟩, ⟨.and,[1,10]⟩, ⟨.or,[7,11]⟩, ⟨.and,[6,12]⟩,
    ⟨.or,[0,13]⟩],14⟩

set_option maxRecDepth 10000 in
theorem upper : Monotone2 witness ∧ witness.size = 9 ∧
    ∀ x, witness.eval (List.ofFn x) = full x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [Monotone2, witness]
  · decide +kernel

theorem exactMinimum : HasCircuitSize 6 full 9 ∧
    (∀ s, HasCircuitSize 6 full s → 9 ≤ s) ∧ Monotone2 witness ∧
    witness.size = 9 ∧ ∀ x, witness.eval (List.ofFn x) = full x := by
  obtain ⟨mono, size, computes⟩ := upper
  have legal : FanInTwo witness := by
    intro g hg
    obtain ⟨op, arity⟩ := mono g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (Or.inl h)), arity⟩
  exact ⟨⟨witness, legal, size.le, computes⟩, fullLower, upper⟩

end Row16752Review
#print axioms Row16752Review.exactMinimum
