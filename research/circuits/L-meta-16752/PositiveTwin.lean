import FreshOutput
import PEqualNP.Outside.L_meta_8642

/-! Input zero is a disjunct of the target. The other five inputs implement
the literal truth table of the upstream theorem L-meta-8642. -/
namespace Row16752
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (BFn relabel relGate rel_fold rel_init relabel_size)
open FreshOutput

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2^32 + 4276808362)
  (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)
def core (x : Fin 5 → Bool) : Bool := Nat.testBit 0xe8a8e880
  (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)
def rotate : Fin 6 → Fin 6 := ![1,2,3,4,5,0]
def inverse : Fin 6 → Fin 6 := ![5,0,1,2,3,4]

set_option maxRecDepth 8192 in
theorem factor : (fun x => adjoin .join core (x ∘ rotate)) = target := by
  funext x; revert x; decide +kernel
set_option maxRecDepth 8192 in
theorem undo : (fun x => target (x ∘ inverse)) = adjoin .join core := by
  funext x; revert x; decide +kernel

/-- Changing input indices preserves an arbitrary specified gate basis and the original budget. -/
theorem basisRelabel {n m s} (π : Fin n → Fin m) (ops : Set GateOp) (f : BFn n)
    (h : Budget ops f s) : Budget ops (fun x => f (x ∘ π)) s := by
  obtain ⟨C,legal,size,ev⟩ := h
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hg
    exact ⟨(legal o ho).1, by simpa [relGate] using (legal o ho).2⟩
  · simpa [relabel, Circuit.size] using size
  · intro x
    exact ((rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output).trans (ev _)

theorem coreNonconstant : Nonconstant core := ⟨fun _ => false, fun _ => true, by decide +kernel⟩

theorem rowBudget (s : ℕ) : HasCircuitSize 6 target s ↔ ∃ t, t+1 ≤ s ∧ HasCircuitSize 5 core t := by
  rw [← budget_iff .join core coreNonconstant]
  constructor
  · intro h
    exact undo ▸ relabel_size inverse target s h
  · intro h
    exact factor ▸ relabel_size rotate (adjoin .join core) s h

theorem positiveTwin (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target x := by
  obtain ⟨t,ht,hcore⟩ := (rowBudget s).mp h
  have best : Mono core t := PEqualNP.Outside.L_meta_8642 t hcore
  have grown := extend .join core {GateOp.and,GateOp.or} (by simp [Kind.op]) best
  obtain ⟨C, hm, hs, he⟩ := basisRelabel rotate _ _ grown
  rw [factor] at he
  exact ⟨C, hm, hs.trans ht, he⟩

theorem assignedNegativeFalse : ¬ (¬ (∀ s, HasCircuitSize 6 target s → ∃ C : Circuit,
    Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target x)) :=
  fun negative => negative positiveTwin

end Row16752
#print axioms Row16752.rowBudget
#print axioms Row16752.positiveTwin
#print axioms Row16752.assignedNegativeFalse
