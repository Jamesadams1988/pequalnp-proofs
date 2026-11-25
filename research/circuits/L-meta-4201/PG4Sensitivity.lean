import Extremal
import ZeroSensitivity

/-! The unrestricted zero-sensitivity lower bound specialized to the literal
L-meta-4201 incidence function and the same gate-counting predicate. -/
namespace PG4Extremal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem unrestricted_or_lower_33 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (33 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false) x1.gates := by
  intro C hm h
  have correct (x : Vertex → Bool) : C.eval (List.ofFn x) = true ↔ Incidence x := h x
  have base : C.eval (List.ofFn witness) = false := by
    cases e : C.eval (List.ofFn witness) with
    | false => rfl
    | true => exact (witness_false ((correct _).mp e)).elim
  have bound := ZeroSensitivity.orCountBound C hm witness zeros base
    (fun v hv => (correct _).mpr (all_flips v hv))
  have ops : ZeroSensitivity.isOr =
      (fun g : Gate => GateOp.casesOn g.op false true false (fun _ => false) false) := by
    funext g
    unfold ZeroSensitivity.isOr
    cases g.op <;> rfl
  rw [zeros_card, ops] at bound
  omega


/-- The same 34 sensitive flips require at least 33 OR gates with two inputs. -/
theorem binary_or_lower_33 (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Vertex → Bool, C.eval (List.ofFn x) = true ↔ Incidence x) :
    33 ≤ C.gates.countP ZeroSensitivity.isBinaryOr := by
  have base : C.eval (List.ofFn witness) = false := by
    cases e : C.eval (List.ofFn witness) with
    | false => rfl
    | true => exact (witness_false ((correct _).mp e)).elim
  have bound := ZeroSensitivity.binaryOrCountBound C hm witness zeros base
    (fun v hv => (correct _).mpr (all_flips v hv))
  rw [zeros_card] at bound
  omega

end PG4Extremal
#print axioms PG4Extremal.unrestricted_or_lower_33
#print axioms PG4Extremal.binary_or_lower_33
