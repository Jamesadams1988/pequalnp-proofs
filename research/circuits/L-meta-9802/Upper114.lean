import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import PEqualNP.Defs.MetaComplexityLgpMono

/-! Specialization of the repository's checked cover-circuit constructor to
the L-meta-9802 incidence graph. Each point owns its listed incident edges. -/
namespace Row9802.Upper114
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit

/-- The listed oriented edges in their original order. -/
def edges : List (ℕ × ℕ) := [
  (0, 20), (0, 25), (0, 27), (0, 37),
  (1, 21), (1, 26), (1, 28), (1, 38),
  (2, 21), (2, 22), (2, 27), (2, 29), (2, 39),
  (3, 20), (3, 22), (3, 23), (3, 28), (3, 30),
  (4, 23), (4, 24), (4, 29), (4, 31),
  (5, 21), (5, 24), (5, 25), (5, 30), (5, 32),
  (6, 22), (6, 25), (6, 26), (6, 31), (6, 33),
  (7, 23), (7, 26), (7, 27), (7, 32), (7, 34),
  (8, 24), (8, 27), (8, 28), (8, 33), (8, 35),
  (9, 25), (9, 28), (9, 29), (9, 34), (9, 36),
  (10, 26), (10, 29), (10, 30), (10, 35), (10, 37),
  (11, 27), (11, 30), (11, 31), (11, 36), (11, 38),
  (12, 28), (12, 31), (12, 32), (12, 37), (12, 39),
  (13, 20), (13, 29), (13, 32), (13, 33), (13, 38),
  (14, 30), (14, 33), (14, 34), (14, 39),
  (15, 20), (15, 21), (15, 31), (15, 34), (15, 35),
  (16, 22), (16, 32), (16, 35), (16, 36),
  (17, 21), (17, 23), (17, 33), (17, 36), (17, 37),
  (18, 22), (18, 24), (18, 34), (18, 37), (18, 38),
  (19, 23), (19, 25), (19, 35), (19, 38), (19, 39)]

def cover : List ℕ := List.range 20

/-- Fan-in-two cover circuit over the 20 point-centered stars. -/
def witness : Circuit := coverCircuit 40 edges cover

theorem gateCounts : witness.size = 114 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) = 94 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) = 20 := by
  decide +kernel

theorem binaryMonotone : Monotone2 witness ∧ ∀ g ∈ witness.gates, g.inputs.length = 2 := by
  have h := gates_ops 40 edges cover
  exact ⟨fun g hg => ⟨(h g hg).1.symm,(h g hg).2.le⟩,fun g hg => (h g hg).2⟩

private theorem rowBounds : edges.all (fun e => decide (e.1 < 20 ∧ e.2 < 40)) = true := by
  decide +kernel

private theorem bounds {e : ℕ × ℕ} (h : e ∈ edges) : e.1 < 20 ∧ e.2 < 40 :=
  of_decide_eq_true (List.all_eq_true.mp rowBounds e h)

private theorem edgesBounded (e : ℕ × ℕ) (h : e ∈ edges) : e.1 < 40 ∧ e.2 < 40 :=
  ⟨by have := (bounds h).1; omega,(bounds h).2⟩

private theorem covered (e : ℕ × ℕ) (h : e ∈ edges) : e.1 ∈ cover ∨ e.2 ∈ cover :=
  .inl (List.mem_range.mpr (bounds h).1)

/-- The upstream block-by-block evaluation proof is symbolic in the 40 input values. -/
theorem computes (x : Fin 40 → Bool) : witness.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 40, (p.val, l.val) ∈ edges ∧
      x p = true ∧ x l = true := by
  have eval := congrFun (circuitFun_eq 40 edges cover edgesBounded covered) x
  change circuitFun 40 (coverCircuit 40 edges cover) x = true ↔ _
  rw [eval, decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,ab | ba,ha,hb⟩
    · exact ⟨a,b,ab,ha,hb⟩
    · exact ⟨b,a,ba,hb,ha⟩
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,.inl h,ha,hb⟩

theorem upperWitness : Monotone2 witness ∧ witness.size = 114 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) = 94 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) = 20 ∧
    ∀ x : Fin 40 → Bool, witness.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 40, (p.val, l.val) ∈ edges ∧
        x p = true ∧ x l = true :=
  ⟨binaryMonotone.1,gateCounts.1,gateCounts.2.1,gateCounts.2.2,computes⟩

end Row9802.Upper114
#print axioms Row9802.Upper114.upperWitness
