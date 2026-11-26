import PEqualNP.MetaComplexity.Helpers.CoverCircuitList

namespace Row9769.PointStars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit

set_option maxRecDepth 24000
set_option maxHeartbeats 3500000

/-- The 104 conjuncts of the desk function in the published order. -/
def finiteEdges : List (Fin 42 × Fin 42) := [
  (0, 26), (0, 28), (0, 38), (0, 41),
  (1, 21), (1, 22), (1, 27), (1, 29), (1, 39),
  (2, 22), (2, 23), (2, 28), (2, 30), (2, 40),
  (3, 23), (3, 24), (3, 29), (3, 31), (3, 41),
  (4, 21), (4, 24), (4, 25), (4, 30), (4, 32),
  (5, 22), (5, 25), (5, 26), (5, 31), (5, 33),
  (6, 23), (6, 26), (6, 27), (6, 32), (6, 34),
  (7, 24), (7, 27), (7, 28), (7, 33), (7, 35),
  (8, 25), (8, 28), (8, 29), (8, 34), (8, 36),
  (9, 26), (9, 29), (9, 30), (9, 35), (9, 37),
  (10, 27), (10, 30), (10, 31), (10, 36), (10, 38),
  (11, 28), (11, 31), (11, 32), (11, 37), (11, 39),
  (12, 29), (12, 32), (12, 33), (12, 38), (12, 40),
  (13, 30), (13, 33), (13, 34), (13, 39), (13, 41),
  (14, 21), (14, 31), (14, 34), (14, 35), (14, 40),
  (15, 22), (15, 32), (15, 35), (15, 36), (15, 41),
  (16, 21), (16, 23), (16, 33), (16, 36), (16, 37),
  (17, 22), (17, 24), (17, 34), (17, 37), (17, 38),
  (18, 23), (18, 25), (18, 35), (18, 38), (18, 39),
  (19, 24), (19, 26), (19, 36), (19, 39), (19, 40),
  (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def edges : List (ℕ × ℕ) := finiteEdges.map (fun e => (e.1.val, e.2.val))

def cover : List ℕ := List.range 21

def witness : Circuit := coverCircuit 42 edges cover

theorem census : witness.size = 124 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) = 21 ∧
    witness.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false) = 103 := by
  decide +kernel

theorem basis : FanInTwo witness := by
  intro g hg
  obtain ⟨hor | hand, hlen⟩ := gates_ops 42 edges cover g hg
  · exact ⟨by simp [hor],hlen.le⟩
  · exact ⟨by simp [hand],hlen.le⟩

private theorem rowBounds : edges.all (fun e => decide (e.1 < 21 ∧ e.2 < 42)) = true := by
  decide +kernel

private theorem bounds {e : ℕ × ℕ} (h : e ∈ edges) : e.1 < 21 ∧ e.2 < 42 :=
  of_decide_eq_true (List.all_eq_true.mp rowBounds e h)

private theorem edgesBounded (e : ℕ × ℕ) (h : e ∈ edges) : e.1 < 42 ∧ e.2 < 42 :=
  ⟨by have := (bounds h).1; omega, (bounds h).2⟩

private theorem covered (e : ℕ × ℕ) (h : e ∈ edges) : e.1 ∈ cover ∨ e.2 ∈ cover :=
  .inl (List.mem_range.mpr (bounds h).1)

theorem computes (x : Fin 42 → Bool) : witness.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 42, (p.val, l.val) ∈ edges ∧ x p = true ∧ x l = true := by
  have ev := congrFun (circuitFun_eq 42 edges cover edgesBounded covered) x
  change circuitFun 42 (coverCircuit 42 edges cover) x = true ↔ _
  rw [ev, decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,h | h,ha,hb⟩
    · exact ⟨a,b,h,ha,hb⟩
    · exact ⟨b,a,h,hb,ha⟩
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,.inl h,ha,hb⟩

private theorem fold_spec {α : Type} (f : α → Bool) (l : List α) (init : Bool) :
    l.foldl (fun a e => a || f e) init = true ↔ init = true ∨ ∃ e ∈ l, f e = true := by
  induction l generalizing init with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih]
    simp only [Bool.or_eq_true, List.mem_cons]
    grind

theorem computesFold (x : Fin 42 → Bool) : witness.eval (List.ofFn x) =
    finiteEdges.foldl (fun a e => a || (x e.1 && x e.2)) false := by
  rw [Bool.eq_iff_iff, computes, fold_spec]
  simp only [Bool.false_eq_true, false_or, Bool.and_eq_true]
  constructor
  · rintro ⟨p,l,member,hp,hl⟩
    obtain ⟨⟨u,v⟩,h,eq⟩ := List.mem_map.mp member
    have hpu : u = p := Fin.ext (congrArg Prod.fst eq)
    have hlv : v = l := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(u,v),h,hpu ▸ hp,hlv ▸ hl⟩
  · rintro ⟨⟨p,l⟩,member,hp,hl⟩
    exact ⟨p,l,List.mem_map.mpr ⟨(p,l),member,rfl⟩,hp,hl⟩

/-- The literal desk DNF, with its gate budget raised by one. -/
theorem literalUpper124 :
  PEqualNP.MetaComplexity.HasCircuitSize 42 (fun x : Fin 42 → Bool => (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) 124 := by
  refine ⟨witness, basis, census.1.le, ?_⟩
  intro x
  exact computesFold x

end Row9769.PointStars
#print axioms Row9769.PointStars.literalUpper124
#print axioms Row9769.PointStars.census
