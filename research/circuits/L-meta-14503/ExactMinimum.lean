import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_9526

/-! The eight-vertex graph in L-meta-14503 contains a four-clique on
vertices 0, 4, 6 and 7. The restrictions below save five gates before
reaching that clique. The elimination and relabeling results are from
L-meta-4795, which credits sanchan's L-meta-927. The four-clique lower
bound is hilelyos's L-meta-9526. -/

namespace L14503Exact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (gate_elim_at one_gate_at relabel_size)
open PEqualNP.Outside.L_meta_9526 (targetK4 lb_K4)

private def edges : List ℕ := [0,4, 1,5, 2,5, 0,6, 3,6, 4,6, 0,7, 1,7, 2,7, 4,7, 6,7]

def edgeFn (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

/-- The four products are (0 ∨ 4)(6 ∨ 7), 0·4, 6(3 ∨ 7), and (1 ∨ 2)(5 ∨ 7). -/
def monoWitness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩,
     ⟨.and, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [6, 12]⟩,
     ⟨.or, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [14, 15]⟩,
     ⟨.or, [10, 11]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem witness_ops :
    ∀ g ∈ monoWitness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [monoWitness]

theorem witness_size : monoWitness.gates.length = 12 := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem witness_eval : ∀ x : Fin 8 → Bool,
    monoWitness.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

private def pin (f : (Fin 8 → Bool) → Bool) (p : Fin 8) (b : Bool) (x : Fin 8 → Bool) :=
  f (Function.update x p b)

private def dropTwin := pin edgeFn 2 false
private def pinLeaf (b : Bool) := pin dropTwin 5 b
private def dropNeighbor (b : Bool) := pin (pinLeaf b) 1 false
private def clique (b : Bool) := pin (dropNeighbor b) 3 false
private def pair04 (i : Fin 8) := decide (i = 0 ∨ i = 4)

private theorem twinEssential : ∃ x, edgeFn (Function.update x 2 (!x 2)) ≠ edgeFn x :=
  ⟨fun i => decide (i = 5), by decide +kernel⟩

private theorem droppedNonconstant : ∃ x y, dropTwin x ≠ dropTwin y :=
  ⟨fun _ => false, pair04, by decide +kernel⟩

private theorem leafEssential : ∃ x, dropTwin (Function.update x 5 (!x 5)) ≠ dropTwin x :=
  ⟨fun i => decide (i = 1), by decide +kernel⟩

private theorem pinnedNonconstant (b : Bool) : ∃ x y, pinLeaf b x ≠ pinLeaf b y := by
  refine ⟨fun _ => false, pair04, ?_⟩
  cases b <;> decide +kernel

private theorem neighborEssential (b : Bool) :
    ∃ x, pinLeaf b (Function.update x 1 (!x 1)) ≠ pinLeaf b x := by
  refine ⟨fun i => decide (i = 7), ?_⟩
  cases b <;> decide +kernel

private theorem neighborDroppedNonconstant (b : Bool) : ∃ x y, dropNeighbor b x ≠ dropNeighbor b y := by
  refine ⟨fun _ => false, pair04, ?_⟩
  cases b <;> decide +kernel

private theorem remainingLeafEssential (b : Bool) :
    ∃ x, dropNeighbor b (Function.update x 3 (!x 3)) ≠ dropNeighbor b x := by
  refine ⟨fun i => decide (i = 6), ?_⟩
  cases b <;> decide +kernel

private theorem cliqueNonconstant (b : Bool) : ∃ x y, clique b x ≠ clique b y := by
  refine ⟨fun _ => false, pair04, ?_⟩
  cases b <;> decide +kernel

private def label : Fin 8 → Fin 4 := ![0,0,0,0,1,0,2,3]

private theorem cliqueEq (b : Bool) : (fun x : Fin 4 → Bool => clique b (x ∘ label)) = targetK4 := by
  funext x
  revert x
  cases b <;> decide +kernel

section Restrictions

attribute [local irreducible] edgeFn

private theorem eliminateTwin {s} (c : HasCircuitSize 8 edgeFn s) :
    ∃ t, t+1 ≤ s ∧ HasCircuitSize 8 dropTwin t :=
  one_gate_at 7 edgeFn 2 false s twinEssential droppedNonconstant c

private theorem eliminateLeaf {s} (c : HasCircuitSize 8 dropTwin s) :
    ∃ b t, t+2 ≤ s ∧ HasCircuitSize 8 (pinLeaf b) t :=
  gate_elim_at 7 dropTwin 5 s leafEssential pinnedNonconstant c

private theorem eliminateNeighbor {s} (b : Bool) (c : HasCircuitSize 8 (pinLeaf b) s) :
    ∃ t, t+1 ≤ s ∧ HasCircuitSize 8 (dropNeighbor b) t :=
  one_gate_at 7 (pinLeaf b) 1 false s (neighborEssential b) (neighborDroppedNonconstant b) c

private theorem eliminateRemainingLeaf {s} (b : Bool) (c : HasCircuitSize 8 (dropNeighbor b) s) :
    ∃ t, t+1 ≤ s ∧ HasCircuitSize 8 (clique b) t :=
  one_gate_at 7 (dropNeighbor b) 3 false s (remainingLeafEssential b) (cliqueNonconstant b) c

private theorem cliqueLower {s} (b : Bool) (c : HasCircuitSize 8 (clique b) s) : 7 ≤ s := by
  have hc : HasCircuitSize 4 (fun x => clique b (x ∘ label)) s :=
    relabel_size label (clique b) s c
  exact lb_K4 s ((cliqueEq b) ▸ hc)

/-- Pin vertex 2 to expose the leaf 5. Eliminating that leaf saves two gates
for one polarity. Pinning its neighbor 1 to false then gives the same graph
in both branches, the four-clique with one leaf at 6. Pin vertex 3 to reach
the four-clique. -/
theorem lower {s : ℕ} (c : HasCircuitSize 8 edgeFn s) : 12 ≤ s := by
  obtain ⟨t, h₁, c₁⟩ := eliminateTwin c
  obtain ⟨b, u, h₂, c₂⟩ := eliminateLeaf c₁
  obtain ⟨v, h₃, c₃⟩ := eliminateNeighbor b c₂
  obtain ⟨w, h₄, c₄⟩ := eliminateRemainingLeaf b c₃
  have hK := cliqueLower b c₄
  clear c c₁ c₂ c₃ c₄
  omega

end Restrictions

theorem exactMinimum :
    HasCircuitSize 8 edgeFn 12 ∧
    (∀ s, HasCircuitSize 8 edgeFn s → 12 ≤ s) ∧
    Monotone2 monoWitness ∧ monoWitness.size = 12 ∧
    ∀ x : Fin 8 → Bool, monoWitness.eval (List.ofFn x) = edgeFn x := by
  have legal : FanInTwo monoWitness := by
    intro g hg
    obtain ⟨hop, har⟩ := witness_ops g hg
    exact ⟨hop.elim Or.inl (fun h => Or.inr (Or.inl h)), har⟩
  exact ⟨⟨monoWitness, legal, le_rfl, witness_eval⟩,
    fun _ c => lower c, witness_ops, rfl, witness_eval⟩

/-- The literal desk proposition asserts a strict saving with at most one NOT.
Its negation follows from the matching unrestricted lower and monotone upper bounds. -/
theorem assignedStatementFalse : ¬ (¬ (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))) := by
  intro claimed
  apply claimed
  intro gates o hFan _hUnique hEval
  have c : HasCircuitSize 8 edgeFn gates.length :=
    ⟨⟨gates, o⟩, hFan, Nat.le_refl _, hEval⟩
  exact ⟨monoWitness.gates, monoWitness.output, witness_ops, lower c, witness_eval⟩

end L14503Exact

#print axioms L14503Exact.exactMinimum
#print axioms L14503Exact.assignedStatementFalse
