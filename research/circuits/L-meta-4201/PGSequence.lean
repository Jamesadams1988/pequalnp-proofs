import PEqualNP.Defs

/-! An explicit alternating Hamiltonian path in the order-four Singer plane.
The order is point 0, line 0, point 1, line 1, ..., point 20, line 20.
The last 40 vertices give successive tests for distinct OR gate charges.
-/
namespace Row4201.PGSequence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incident (p l : Fin 42) : Prop :=
  p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ [0,5,7,17,20]
instance (p l : Fin 42) : Decidable (incident p l) := by unfold incident; infer_instance

def accepts (x : Fin 42 → Bool) : Prop :=
  ∃ p l, incident p l ∧ x p = true ∧ x l = true
instance (x : Fin 42 → Bool) : Decidable (accepts x) := by unfold accepts; infer_instance

def rank (v : Fin 42) : ℕ := if v.val < 21 then 2*v.val else 2*(v.val-21)+1

def pref (k : ℕ) (v : Fin 42) : Bool := decide (rank v < k+2)
def witness (k : Fin 40) (v : Fin 42) : Bool := decide (rank v = k.val+1 ∨ rank v = k.val+2)

theorem prefixMono {i j : ℕ} (h : i ≤ j) (v : Fin 42) (hv : pref i v = true) :
    pref j v = true := by
  simp only [pref, decide_eq_true_eq] at *
  omega

theorem witnessNext (k : Fin 40) (v : Fin 42) (hv : witness k v = true) :
    pref (k.val+1) v = true := by
  simp only [pref, witness, decide_eq_true_eq] at *
  omega

theorem prefixAccepts (k : Fin 40) : accepts (pref k.val) := by
  refine ⟨0,21,by decide,?_,?_⟩ <;> simp [pref,rank]

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem witnessAccepts : ∀ k : Fin 40, accepts (witness k) := by decide +kernel

theorem meetRejects : ∀ k : Fin 40, ¬ accepts (fun v => pref k.val v && witness k v) :=
  by decide +kernel

/-- The hypotheses in the precise form consumed by the OR charging argument. -/
theorem samples (C : Circuit) (hf : ∀ x, C.eval (List.ofFn x) = true ↔ accepts x) (k : Fin 40) :
    C.eval (List.ofFn (pref k.val)) = true ∧
    C.eval (List.ofFn (witness k)) = true ∧
    C.eval (List.ofFn (fun v => pref k.val v && witness k v)) = false := by
  refine ⟨(hf _).mpr (prefixAccepts k), (hf _).mpr (witnessAccepts k), ?_⟩
  cases he : C.eval (List.ofFn (fun v => pref k.val v && witness k v)) with
  | false => rfl
  | true => exact (meetRejects k ((hf _).mp he)).elim

end Row4201.PGSequence
#print axioms Row4201.PGSequence.samples
