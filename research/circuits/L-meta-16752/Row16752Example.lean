import FreshOutputAt
import PEqualNP.Outside.L_meta_8642

/-! Row 16752 is the disjunction of its first input and the five-input function
of L-meta-8642. The other five coordinates keep their natural order. -/
namespace Row16752Example
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FreshOutput FreshOutputAt

abbrev core := PEqualNP.Outside.L_meta_8642.targetFun 0xe8a8e880

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276809450 * 2^32 + 4276808362)
    (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)

set_option maxRecDepth 8192 in
theorem factor : target = atInput 0 .join core := funext (by decide +kernel)

/-- The existing five-input replacement theorem transfers to every six-input budget. -/
theorem replacement (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target x := by
  rw [factor] at h ⊢
  exact FreshOutputAt.replacement 0 .join core
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩ PEqualNP.Outside.L_meta_8642 s h

end Row16752Example
#print axioms Row16752Example.replacement
