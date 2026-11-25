import HexNormalize

/-! Normalize the physical AND/OR gate list to conjunction selectors and a
chronological sequence of binary ORs. The wire invariant covers every natural
index, so a forward reference, an invalid output, or an absent operand reads false. -/
namespace HexNormalize
open Row4201.HexFour PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def argument (w : List Bool) : Option ℕ → Bool
  | none => false
  | some i => w.getD i false

private theorem argumentHas {k} (hk : k ≤ 4) (c : Code k) (w : BitVec 6 → List Bool)
    (hw : Rep c w) (index : Option ℕ) : Has c (fun x => argument (w x) index) := by
  cases index with
  | none => exact bot hk c
  | some i => exact hw i

private theorem binaryOr (g : Gate) (op : g.op = .or) (arity : g.inputs.length ≤ 2)
    (w : List Bool) : gate w g =
      (argument w g.inputs[0]? || argument w g.inputs[1]?) := by
  rcases g with ⟨op', ins⟩
  obtain rfl : op' = GateOp.or := op
  cases ins with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => simp [gate,argument,GateOp.eval]
    | cons b xs =>
      cases xs with
      | nil => simp [gate,argument,GateOp.eval]
      | cons u us => simp at arity

/-- Starting with the current representations of the physical wires, processing
the remaining list introduces one abstract instruction for each physical OR.
No topological index or positive-arity hypothesis is required. -/
theorem foldToCode (gs : List Gate) {k : ℕ} (c : Code k) (w : BitVec 6 → List Bool)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (budget : k + gs.countP ZeroSensitivity.isOr ≤ 4)
    (len : ∀ x, (w x).length = (w 0).length) (rep : Rep c w) :
    ∃ (j : ℕ) (u : Code j), j = k + gs.countP ZeroSensitivity.isOr ∧
      Rep u (fun x => gs.foldl addWire (w x)) := by
  induction gs generalizing k w with
  | nil => exact ⟨k,c,rfl,rep⟩
  | cons g gs ih =>
    have tail := fun q (hq : q ∈ gs) => hm q (List.mem_cons_of_mem g hq)
    obtain ⟨op,arity⟩ := hm g List.mem_cons_self
    have hk : k ≤ 4 := by omega
    let w' := fun x => addWire (w x) g
    have len' (x) : (w' x).length = (w' 0).length := by
      simp only [w', addWire, List.length_append, List.length_cons,List.length_nil,len x]
    rcases op with ha | ho
    · have count : (g::gs).countP ZeroSensitivity.isOr = gs.countP ZeroSensitivity.isOr := by
        simp [ZeroSensitivity.isOr,ha]
      have val : Has c (fun x => gate (w x) g) := by
        simpa [gate,ha,GateOp.eval] using allHas hk c w rep g.inputs
      exact count ▸ ih c w' tail (by omega) len' (updated c w len rep g val)
    · have count : (g::gs).countP ZeroSensitivity.isOr = gs.countP ZeroSensitivity.isOr + 1 := by
        simp [ZeroSensitivity.isOr,ho]
      obtain ⟨l,r,hnew⟩ := orPush hk c (argumentHas hk c w rep g.inputs[0]?)
        (argumentHas hk c w rep g.inputs[1]?)
      have val : Has (c.push l r) (fun x => gate (w x) g) := by
        simpa only [binaryOr g ho arity] using hnew
      have lifted : Rep (c.push l r) w := fun i => lift hk c l r (rep i)
      obtain ⟨j,u,hj,rep'⟩ := ih (c.push l r) w' tail (by omega) len'
        (updated (c.push l r) w len lifted g val)
      exact ⟨j,u,by omega,rep'⟩

/-- Specialization to the official evaluator on any family of equal-length
physical input vectors whose entries are available in the initial bank. -/
theorem circuitToCode (C : Circuit) (hm : Monotone2 C)
    (budget : C.gates.countP ZeroSensitivity.isOr ≤ 4) (w : BitVec 6 → List Bool)
    (len : ∀ x, (w x).length = (w 0).length) (inputs : Rep .start w) :
    ∃ (j : ℕ) (u : Code j), j = C.gates.countP ZeroSensitivity.isOr ∧
      Rep u (fun x => C.wires (w x)) ∧ Has u (fun x => C.eval (w x)) := by
  obtain ⟨j,u,hj,all⟩ := foldToCode C.gates .start w hm (by simpa using budget) len inputs
  exact ⟨j,u,by simpa using hj,all,all C.output⟩

end HexNormalize

#print axioms HexNormalize.circuitToCode
