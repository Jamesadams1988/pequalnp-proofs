import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import PEqualNP.Defs.MetaComplexityLgpMono

/-! Specialization of the repository's checked cover-circuit constructor to
the L-meta-4201 incidence graph. Each point owns its five incident edges. -/
namespace Row4201.Upper125
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit

def offsets : List ℕ := [0,5,7,17,20]

def incidenceEdges : List (ℕ × ℕ) := (List.range 21).flatMap (fun p =>
  offsets.map (fun d => (p,21+(p+d)%21)))

def cover : List ℕ := List.range 21

/-- Each of the 21 stars costs four ORs and one AND. The final chain costs 20 ORs. -/
def witness : Circuit := coverCircuit 42 incidenceEdges cover

theorem gateCounts : witness.size = 125 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) = 104 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) = 21 := by
  decide +kernel

theorem binaryMonotone : Monotone2 witness ∧ ∀ g ∈ witness.gates, g.inputs.length = 2 := by
  have h := gates_ops 42 incidenceEdges cover
  exact ⟨fun g hg => ⟨(h g hg).1.symm,(h g hg).2.le⟩,fun g hg => (h g hg).2⟩

private theorem edgesBounded (e : ℕ × ℕ) (h : e ∈ incidenceEdges) :
    e.1 < 42 ∧ e.2 < 42 := by
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hm
  have lt := List.mem_range.mp hp
  simp only
  constructor <;> omega

private theorem covered (e : ℕ × ℕ) (h : e ∈ incidenceEdges) : e.1 ∈ cover ∨ e.2 ∈ cover := by
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hm
  exact .inl hp

set_option maxRecDepth 8192 in
private theorem pairSpec : ∀ p l : Fin 42, (p.val,l.val) ∈ incidenceEdges ↔
    p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ [0,5,7,17,20] := by decide +kernel

/-- The upstream block-by-block evaluation proof is symbolic in the 42 input values. -/
theorem computes (x : Fin 42 → Bool) : witness.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ [0,5,7,17,20]) ∧
      x p = true ∧ x l = true := by
  have eval := congrFun (circuitFun_eq 42 incidenceEdges cover edgesBounded covered) x
  change circuitFun 42 (coverCircuit 42 incidenceEdges cover) x = true ↔ _
  rw [eval, decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,ab | ba,ha,hb⟩
    · exact ⟨a,b,(pairSpec a b).mp ab,ha,hb⟩
    · exact ⟨b,a,(pairSpec b a).mp ba,hb,ha⟩
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,.inl ((pairSpec a b).mpr h),ha,hb⟩

theorem upperWitness : Monotone2 witness ∧ witness.size = 125 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) = 104 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) = 21 ∧
    ∀ x : Fin 42 → Bool, witness.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ [0,5,7,17,20]) ∧
        x p = true ∧ x l = true :=
  ⟨binaryMonotone.1,gateCounts.1,gateCounts.2.1,gateCounts.2.2,computes⟩

end Row4201.Upper125
#print axioms Row4201.Upper125.upperWitness
