import PEqualNP.Defs

namespace ProjectivePrefix1988
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32000
set_option maxHeartbeats 12000000

def circ : Circuit :=
  ⟨[⟨.or, [13, 15]⟩, ⟨.or, [26, 21]⟩, ⟨.or, [27, 25]⟩, ⟨.and, [1, 28]⟩,
    ⟨.or, [14, 20]⟩, ⟨.or, [30, 24]⟩, ⟨.or, [31, 25]⟩, ⟨.and, [2, 32]⟩,
    ⟨.or, [13, 19]⟩, ⟨.or, [34, 23]⟩, ⟨.or, [35, 24]⟩, ⟨.and, [3, 36]⟩,
    ⟨.or, [18, 22]⟩, ⟨.or, [38, 23]⟩, ⟨.or, [39, 25]⟩, ⟨.and, [4, 40]⟩,
    ⟨.or, [17, 21]⟩, ⟨.or, [42, 22]⟩, ⟨.or, [43, 24]⟩, ⟨.and, [5, 44]⟩,
    ⟨.or, [16, 20]⟩, ⟨.or, [46, 21]⟩, ⟨.or, [47, 23]⟩, ⟨.and, [6, 48]⟩,
    ⟨.or, [15, 19]⟩, ⟨.or, [50, 20]⟩, ⟨.or, [51, 22]⟩, ⟨.and, [7, 52]⟩,
    ⟨.or, [14, 18]⟩, ⟨.or, [54, 19]⟩, ⟨.or, [55, 21]⟩, ⟨.and, [8, 56]⟩,
    ⟨.or, [13, 17]⟩, ⟨.or, [58, 18]⟩, ⟨.or, [59, 20]⟩, ⟨.and, [9, 60]⟩,
    ⟨.or, [16, 17]⟩, ⟨.or, [62, 19]⟩, ⟨.or, [63, 25]⟩, ⟨.and, [10, 64]⟩,
    ⟨.or, [15, 16]⟩, ⟨.or, [66, 18]⟩, ⟨.or, [67, 24]⟩, ⟨.and, [11, 68]⟩,
    ⟨.or, [14, 15]⟩, ⟨.or, [70, 17]⟩, ⟨.or, [71, 23]⟩, ⟨.and, [12, 72]⟩,
    ⟨.or, [29, 33]⟩, ⟨.or, [74, 37]⟩, ⟨.or, [75, 41]⟩, ⟨.or, [76, 45]⟩,
    ⟨.or, [77, 49]⟩, ⟨.or, [78, 53]⟩, ⟨.or, [79, 57]⟩, ⟨.or, [80, 61]⟩,
    ⟨.or, [81, 65]⟩, ⟨.or, [82, 69]⟩, ⟨.or, [83, 73]⟩, ⟨.or, [13, 14]⟩,
    ⟨.or, [85, 16]⟩, ⟨.or, [86, 22]⟩, ⟨.or, [84, 0]⟩, ⟨.or, [84, 87]⟩], 89⟩

theorem size_and_basis : circ.size = 64 ∧ Monotone2 circ := by
  refine ⟨rfl, ?_⟩
  simp [circ, Monotone2]

def common (x : Fin 26 → Bool) : Bool :=
  (x 1 && (x 13 || x 15 || x 21 || x 25)) ||
  (x 2 && (x 14 || x 20 || x 24 || x 25)) ||
  (x 3 && (x 13 || x 19 || x 23 || x 24)) ||
  (x 4 && (x 18 || x 22 || x 23 || x 25)) ||
  (x 5 && (x 17 || x 21 || x 22 || x 24)) ||
  (x 6 && (x 16 || x 20 || x 21 || x 23)) ||
  (x 7 && (x 15 || x 19 || x 20 || x 22)) ||
  (x 8 && (x 14 || x 18 || x 19 || x 21)) ||
  (x 9 && (x 13 || x 17 || x 18 || x 20)) ||
  (x 10 && (x 16 || x 17 || x 19 || x 25)) ||
  (x 11 && (x 15 || x 16 || x 18 || x 24)) ||
  (x 12 && (x 14 || x 15 || x 17 || x 23))

def lines0 (x : Fin 26 → Bool) : Bool :=
  (x 13 || x 14 || x 16 || x 22)

def formula (x : Fin 26 → Bool) : Bool :=
  common x || (x 0 && lines0 x)

private theorem inputs (x : Fin 26 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := rfl

theorem terminals (x : Fin 26 → Bool) :
    (circ.wires (List.ofFn x)).getD 88 false = (common x || x 0) ∧
    (circ.wires (List.ofFn x)).getD 89 false = (common x || lines0 x) := by
  rw [inputs]
  simp [circ, Circuit.wires, GateOp.eval, List.getD, common, lines0]

theorem free_output (x : Fin 26 → Bool) :
    GateOp.and.eval ([88, 89].map fun i => (circ.wires (List.ofFn x)).getD i false) =
      formula x := by
  have ⟨h₁, h₂⟩ := terminals x
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, h₁, h₂]
  unfold formula
  cases common x <;> rfl


/-- Edges use the input-wire coordinates of both endpoints. -/
def edges : List (Fin 26 × Fin 26) :=
  [(1, 13), (1, 15), (1, 21), (1, 25),
   (2, 14), (2, 20), (2, 24), (2, 25),
   (3, 13), (3, 19), (3, 23), (3, 24),
   (4, 18), (4, 22), (4, 23), (4, 25),
   (5, 17), (5, 21), (5, 22), (5, 24),
   (6, 16), (6, 20), (6, 21), (6, 23),
   (7, 15), (7, 19), (7, 20), (7, 22),
   (8, 14), (8, 18), (8, 19), (8, 21),
   (9, 13), (9, 17), (9, 18), (9, 20),
   (10, 16), (10, 17), (10, 19), (10, 25),
   (11, 15), (11, 16), (11, 18), (11, 24),
   (12, 14), (12, 15), (12, 17), (12, 23),
   (0, 13), (0, 14), (0, 16), (0, 22)]

theorem edges_spec : ∀ p l : Fin 26, (p, l) ∈ edges ↔
    p.val < 13 ∧ 13 ≤ l.val ∧ (p.val + l.val) % 13 ∈ [0, 1, 3, 9] := by decide

theorem formula_eq_edges (x : Fin 26 → Bool) :
    formula x = edges.any (fun e => x e.1 && x e.2) := by
  simp [formula, common, lines0, edges, Bool.and_or_distrib_left]
  ac_rfl

/-- The two actual designated wires compute precisely the incidence predicate, on all inputs. -/
theorem free_output_spec (x : Fin 26 → Bool) :
    GateOp.and.eval ([88, 89].map fun i => (circ.wires (List.ofFn x)).getD i false) = true ↔
      ∃ p l : Fin 26, p.val < 13 ∧ 13 ≤ l.val ∧ (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧
        x p = true ∧ x l = true := by
  rw [free_output, formula_eq_edges, List.any_eq_true]
  constructor
  · rintro ⟨⟨p, l⟩, he, h⟩
    obtain ⟨hp, hl, hi⟩ := (edges_spec p l).1 he
    exact ⟨p, l, hp, hl, hi, Bool.and_eq_true_iff.mp h⟩
  · rintro ⟨p, l, hp, hl, hi, h₁, h₂⟩
    exact ⟨(p, l), (edges_spec p l).2 ⟨hp, hl, hi⟩, Bool.and_eq_true_iff.mpr ⟨h₁, h₂⟩⟩

end ProjectivePrefix1988
