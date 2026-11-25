import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_8650

/-! Single-operand insertion into the literal seven-gate L-meta-8650 witness.
The proof uses its unrestricted lower bound and the gate elimination lemma from
Nico Habets's L-meta-4795, originating in sanchan's L-meta-927. -/

namespace EdgeExtensions
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8650_aux (targetFunction witnessCircuit)
open PEqualNP.Outside.L_meta_4795_aux (gate_elim_one)

abbrev Edit := Fin 7 × Fin 2 × Bool

/-- Replace one operand of one old gate with its AND (true) or OR (false)
with the new input x5. All other occurrences retain the same value. -/
def expanded (e : Edit) : Circuit :=
  let rename (w : ℕ) := if w < 5 then w else w + 1 + (if 5 + e.1.val ≤ w then 1 else 0)
  let gates := witnessCircuit.gates.zipIdx.flatMap fun (g, j) =>
    let ins := g.inputs.map rename
    if j = e.1.val then
      let op : GateOp := if e.2.2 then .and else .or
      [⟨op, [ins.getD e.2.1.val 0, 5]⟩, ⟨g.op, ins.set e.2.1.val (6 + j)⟩]
    else [⟨g.op, ins⟩]
  ⟨gates, 13⟩

def fn (e : Edit) (x : Fin 6 → Bool) := (expanded e).eval (List.ofFn x)
def row (r : Fin 32) (i : Fin 6) := r.val.testBit i.val

set_option maxRecDepth 24000
set_option maxHeartbeats 0

theorem neutral : ∀ e : Edit, ∀ y, fn e (Fin.snoc y e.2.2) = targetFunction y := by
  decide +kernel

theorem essential : ∀ e : Edit, ∃ r : Fin 32,
    fn e (Function.update (row r) (Fin.last 5) (!(row r (Fin.last 5)))) ≠ fn e (row r) := by
  decide +kernel

def isMonotoneOp : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem shape : ∀ e : Edit, (expanded e).size = 8 ∧
    (expanded e).gates.all (fun g => isMonotoneOp g.op && decide (g.inputs.length ≤ 2)) := by
  decide +kernel

theorem exactMinimum (e : Edit) : Monotone2 (expanded e) ∧ (expanded e).size = 8 ∧
    HasCircuitSize 6 (fn e) 8 ∧ ∀ s, HasCircuitSize 6 (fn e) s → 8 ≤ s := by
  obtain ⟨sz, test⟩ := shape e
  have hm : Monotone2 (expanded e) := by
    intro g hg
    have := List.all_eq_true.mp test g hg
    cases hh : g.op <;> simp_all [isMonotoneOp]
  have hfan : FanInTwo (expanded e) := by
    intro g hg
    obtain ⟨op, ar⟩ := hm g hg
    exact ⟨op.elim Or.inl (fun ho => Or.inr (Or.inl ho)), ar⟩
  refine ⟨hm, sz, ⟨expanded e, hfan, sz.le, fun _ => rfl⟩, ?_⟩
  intro s h
  obtain ⟨r, hr⟩ := essential e
  have nc : ∃ y z, fn e (Fin.snoc y e.2.2) ≠ fn e (Fin.snoc z e.2.2) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    simp only [neutral]
    decide +kernel
  obtain ⟨t, ht, htSize⟩ := gate_elim_one 5 (fn e) e.2.2 s ⟨row r, hr⟩ nc h
  rw [funext (neutral e)] at htSize
  obtain ⟨C, legal, size, computes⟩ := htSize
  have seven := (PEqualNP.Outside.L_meta_8650_aux.lower C legal computes).trans size
  omega

end EdgeExtensions
#print axioms EdgeExtensions.exactMinimum
