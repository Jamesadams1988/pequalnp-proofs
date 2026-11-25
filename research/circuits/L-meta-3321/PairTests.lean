import PEqualNP.Defs

namespace PairTestObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] lineDegreeGateOpDecEq

def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩
def sample : Circuit :=
  ⟨[gate .or 5 1, gate .and 4 6, gate .or 3 7, gate .and 0 8, gate .or 3 2,
    gate .and 9 10, gate .and 1 7, gate .and 2 5, gate .or 11 12, gate .or 14 13],15⟩
def edgeFn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)
def input (mask : ℕ) : Fin 6 → Bool := fun i => mask.testBit i
def wire (x : Fin 6 → Bool) (j : ℕ) := (sample.wires (List.ofFn x)).getD (6+j) false
def andAt (j : Fin 10) := (NestedCover.gateAt sample j).op = GateOp.and

/-- Forcing an internal gate preserves all wire numbers and replaces its output by the requested constant. -/
def force (j : Fin 10) (b : Bool) : Circuit :=
  ⟨sample.gates.set j (if b then ⟨.and,[]⟩ else ⟨.or,[]⟩),sample.output⟩

theorem graph_has_no_four_cycle : ∀ p q a b : Fin 3, p ≠ q → a ≠ b →
    ¬ (p = a ∧ p = b ∧ q = a ∧ q = b) := by decide

theorem legal : Monotone2 sample ∧ NestedCover.ReadsBack 6 sample := by
  constructor
  · simp [sample,gate,Monotone2]
  · decide +kernel

theorem exact_output : ∀ x : Fin 6 → Bool, sample.eval (List.ofFn x) = edgeFn x := by decide +kernel

theorem exact_incidence : ∀ x : Fin 6 → Bool, circuitFun 6 sample x = true ↔
    ∃ p l : Fin 3, p = l ∧ x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true := by decide +kernel

theorem all_pair_tests : ∀ j : Fin 10, andAt j →
    (∀ i : Fin 6, wire (fun k => decide (k=i)) j = false) ∧
    (∀ p l : Fin 3, p ≠ l → wire (fun k => decide (k=Fin.castAdd 3 p ∨ k=Fin.natAdd 3 l)) j = false) := by
  unfold andAt
  decide +kernel

/-- Mask 49 is point 0 and lines 1 and 2. Its pure restrictions are masks 1 and 48. -/
theorem dirty :
    andAt 3 ∧ wire (input 49) 3 = true ∧ wire (input 1) 3 = false ∧
    wire (input 48) 3 = false ∧ edgeFn (input 49) = false := by unfold andAt; decide

theorem dirty_essential_both_ways :
    (force 3 false).eval (List.ofFn (input 9)) ≠ sample.eval (List.ofFn (input 9)) ∧
    (force 3 true).eval (List.ofFn (input 8)) ≠ sample.eval (List.ofFn (input 8)) := by decide

theorem every_gate_matters : ∀ (j : Fin 10) (b : Bool), ∃ x : Fin 6 → Bool,
    (force j b).eval (List.ofFn x) ≠ sample.eval (List.ofFn x) := by decide +kernel

theorem fail_clean_clause :
    ∃ (j : Fin 10) (z : Fin 6 → Bool), andAt j ∧ wire z j = true ∧
      wire (fun k => decide (k.val < 3) && z k) j = false ∧
      wire (fun k => decide (3 ≤ k.val) && z k) j = false ∧
      ¬ (∃ p l : Fin 3, p = l ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) := by
  refine ⟨3,input 49,?_⟩
  unfold andAt
  decide

/-- The graph itself has a smaller clean circuit: an AND per edge and two ORs. -/
def cleanControl : Circuit :=
  ⟨[gate .and 0 3,gate .and 1 4,gate .or 6 7,gate .and 2 5,gate .or 8 9],10⟩

theorem clean_alternative :
    cleanControl.size = 5 ∧ cleanControl.size ≤ sample.size ∧
    (∀ x : Fin 6 → Bool, cleanControl.eval (List.ofFn x) = edgeFn x) ∧
    (∀ (j : Fin 5) (x : Fin 6 → Bool), (NestedCover.gateAt cleanControl j).op = .and →
      (cleanControl.wires (List.ofFn x)).getD (6+j) false = true → edgeFn x = true) ∧
    (∀ (j : Fin 5) (i : Fin 6), (NestedCover.gateAt cleanControl j).op = .and →
      (cleanControl.wires (List.ofFn (fun k => decide (k=i)))).getD (6+j) false = false) := by
  decide +kernel

#print axioms clean_alternative
#print axioms fail_clean_clause
#print axioms all_pair_tests
#print axioms every_gate_matters
end PairTestObstruction
