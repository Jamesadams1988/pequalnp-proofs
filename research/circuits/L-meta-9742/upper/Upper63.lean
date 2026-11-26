import PEqualNP.Defs

namespace ProjectiveEdge9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32000
set_option maxHeartbeats 12000000

/-- Each point gates the balanced OR of its neighbors. The output is a balanced
OR of the thirteen resulting stars. -/
def circuit : Circuit :=
  ⟨[⟨.or, [17, 23]⟩, ⟨.or, [26, 25]⟩, ⟨.and, [0, 27]⟩, ⟨.or, [13, 14]⟩,
    ⟨.or, [18, 24]⟩, ⟨.or, [29, 30]⟩, ⟨.and, [1, 31]⟩, ⟨.or, [14, 15]⟩,
    ⟨.or, [19, 25]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [2, 35]⟩, ⟨.or, [13, 15]⟩,
    ⟨.or, [16, 20]⟩, ⟨.or, [37, 38]⟩, ⟨.and, [3, 39]⟩, ⟨.or, [14, 16]⟩,
    ⟨.or, [17, 21]⟩, ⟨.or, [41, 42]⟩, ⟨.and, [4, 43]⟩, ⟨.or, [15, 17]⟩,
    ⟨.or, [18, 22]⟩, ⟨.or, [45, 46]⟩, ⟨.and, [5, 47]⟩, ⟨.or, [16, 18]⟩,
    ⟨.or, [19, 23]⟩, ⟨.or, [49, 50]⟩, ⟨.and, [6, 51]⟩, ⟨.or, [17, 19]⟩,
    ⟨.or, [20, 24]⟩, ⟨.or, [53, 54]⟩, ⟨.and, [7, 55]⟩, ⟨.or, [18, 20]⟩,
    ⟨.or, [21, 25]⟩, ⟨.or, [57, 58]⟩, ⟨.and, [8, 59]⟩, ⟨.or, [13, 19]⟩,
    ⟨.or, [21, 22]⟩, ⟨.or, [61, 62]⟩, ⟨.and, [9, 63]⟩, ⟨.or, [14, 20]⟩,
    ⟨.or, [22, 23]⟩, ⟨.or, [65, 66]⟩, ⟨.and, [10, 67]⟩, ⟨.or, [15, 21]⟩,
    ⟨.or, [23, 24]⟩, ⟨.or, [69, 70]⟩, ⟨.and, [11, 71]⟩, ⟨.or, [16, 22]⟩,
    ⟨.or, [24, 25]⟩, ⟨.or, [73, 74]⟩, ⟨.and, [12, 75]⟩, ⟨.or, [28, 32]⟩,
    ⟨.or, [36, 40]⟩, ⟨.or, [44, 48]⟩, ⟨.or, [52, 56]⟩, ⟨.or, [60, 64]⟩,
    ⟨.or, [68, 72]⟩, ⟨.or, [77, 78]⟩, ⟨.or, [79, 80]⟩, ⟨.or, [81, 82]⟩,
    ⟨.or, [83, 84]⟩, ⟨.or, [85, 76]⟩, ⟨.or, [86, 87]⟩], 88⟩


theorem parameters : Monotone2 circuit ∧ circuit.size = 63 ∧ circuit.depth 26 = 7 := by
  refine ⟨?_, rfl, by decide⟩
  simp [circuit, Monotone2]

def edges : List (ℕ × ℕ) :=
  [(0, 17), (0, 23), (0, 25),
   (1, 13), (1, 14), (1, 18), (1, 24),
   (2, 14), (2, 15), (2, 19), (2, 25),
   (3, 13), (3, 15), (3, 16), (3, 20),
   (4, 14), (4, 16), (4, 17), (4, 21),
   (5, 15), (5, 17), (5, 18), (5, 22),
   (6, 16), (6, 18), (6, 19), (6, 23),
   (7, 17), (7, 19), (7, 20), (7, 24),
   (8, 18), (8, 20), (8, 21), (8, 25),
   (9, 13), (9, 19), (9, 21), (9, 22),
   (10, 14), (10, 20), (10, 22), (10, 23),
   (11, 15), (11, 21), (11, 23), (11, 24),
   (12, 16), (12, 22), (12, 24), (12, 25)]

private def finiteEdges : List (Fin 26 × Fin 26) :=
  [(0, 17), (0, 23), (0, 25),
   (1, 13), (1, 14), (1, 18), (1, 24),
   (2, 14), (2, 15), (2, 19), (2, 25),
   (3, 13), (3, 15), (3, 16), (3, 20),
   (4, 14), (4, 16), (4, 17), (4, 21),
   (5, 15), (5, 17), (5, 18), (5, 22),
   (6, 16), (6, 18), (6, 19), (6, 23),
   (7, 17), (7, 19), (7, 20), (7, 24),
   (8, 18), (8, 20), (8, 21), (8, 25),
   (9, 13), (9, 19), (9, 21), (9, 22),
   (10, 14), (10, 20), (10, 22), (10, 23),
   (11, 15), (11, 21), (11, 23), (11, 24),
   (12, 16), (12, 22), (12, 24), (12, 25)]


private theorem edges_map :
    edges = finiteEdges.map (fun e => (e.1.val, e.2.val)) := rfl

private def formula (x : Fin 26 → Bool) : Bool :=
  (((((x 0 && ((x 17 || x 23) || x 25)) ||
  (x 1 && ((x 13 || x 14) || (x 18 || x 24)))) ||
  ((x 2 && ((x 14 || x 15) || (x 19 || x 25))) ||
  (x 3 && ((x 13 || x 15) || (x 16 || x 20))))) ||
  (((x 4 && ((x 14 || x 16) || (x 17 || x 21))) ||
  (x 5 && ((x 15 || x 17) || (x 18 || x 22)))) ||
  ((x 6 && ((x 16 || x 18) || (x 19 || x 23))) ||
  (x 7 && ((x 17 || x 19) || (x 20 || x 24)))))) ||
  ((((x 8 && ((x 18 || x 20) || (x 21 || x 25))) ||
  (x 9 && ((x 13 || x 19) || (x 21 || x 22)))) ||
  ((x 10 && ((x 14 || x 20) || (x 22 || x 23))) ||
  (x 11 && ((x 15 || x 21) || (x 23 || x 24))))) ||
  (x 12 && ((x 16 || x 22) || (x 24 || x 25)))))

private theorem input_list (x : Fin 26 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := rfl

private theorem eval_formula (x : Fin 26 → Bool) : circuit.eval (List.ofFn x) = formula x := by
  rw [input_list]
  simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD, formula]

private theorem formula_edges (x : Fin 26 → Bool) :
    formula x = finiteEdges.any (fun e => x e.1 && x e.2) := by
  simp [formula, finiteEdges, Bool.and_or_distrib_left]
  ac_rfl

theorem computes (x : Fin 26 → Bool) :
    circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  rw [eval_formula, formula_edges, List.any_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, he, hv⟩
    refine ⟨u, v, ?_, Bool.and_eq_true_iff.mp hv⟩
    rw [edges_map]
    exact List.mem_map.mpr ⟨(u, v), he, rfl⟩
  · rintro ⟨u, v, he, hu, hv⟩
    rw [edges_map] at he
    obtain ⟨⟨p, q⟩, hm, hpq⟩ := List.mem_map.mp he
    have hp : p = u := Fin.ext (congrArg Prod.fst hpq)
    have hq : q = v := Fin.ext (congrArg Prod.snd hpq)
    subst p
    subst q
    exact ⟨(u, v), hm, Bool.and_eq_true_iff.mpr ⟨hu, hv⟩⟩

theorem upper :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 63 ∧ C.depth 26 = 7 ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true :=
  ⟨circuit, parameters.1, parameters.2.1, parameters.2.2, computes⟩

end ProjectiveEdge9742
