import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9791_control54

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev DNF := List (List ℕ)

def value (x : ℕ → Bool) (d : DNF) : Bool :=
  d.any (fun term => term.all x)

def meet (d e : DNF) : DNF :=
  d.flatMap (fun s => e.map (fun t => s ++ t))

theorem value_meet (x : ℕ → Bool) (d e : DNF) :
    value x (meet d e) = (value x d && value x e) := by
  apply Bool.eq_iff_iff.mpr
  simp only [value, meet, List.any_eq_true, List.mem_flatMap, List.mem_map,
    Bool.and_eq_true]
  constructor
  · rintro ⟨z, ⟨s, hs, t, ht, rfl⟩, h⟩
    simp only [List.all_append, Bool.and_eq_true] at h
    exact ⟨⟨s, hs, h.1⟩, ⟨t, ht, h.2⟩⟩
  · rintro ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
    exact ⟨s ++ t, ⟨s, hs, t, ht, rfl⟩, by simp [hxs, hxt]⟩

theorem value_append (x : ℕ → Bool) (d e : DNF) :
    value x (d ++ e) = (value x d || value x e) := List.any_append

def covers (d e : DNF) : Bool :=
  d.all (fun t => e.any (fun s => s.all (fun i => decide (i ∈ t))))

theorem covers_sound {d e : DNF} (h : covers d e = true) (x : ℕ → Bool) :
    value x d = true → value x e = true := by
  simp only [covers, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  simp only [value, List.any_eq_true, List.all_eq_true]
  rintro ⟨t, ht, hxt⟩
  obtain ⟨s, hs, hst⟩ := h t ht
  exact ⟨s, hs, fun i hi => hxt i (hst i hi)⟩

structure BinaryGate where
  isAnd : Bool
  left : ℕ
  right : ℕ

def BinaryGate.toGate (g : BinaryGate) : Gate :=
  ⟨if g.isAnd then .and else .or, [g.left, g.right]⟩

def BinaryGate.run (g : BinaryGate) (w : List DNF) : DNF :=
  let a := w.getD g.left []
  let b := w.getD g.right []
  if g.isAnd then meet a b else a ++ b

theorem getD_map_value (x : ℕ → Bool) (w : List DNF) (i : ℕ) :
    (w.map (value x)).getD i false = value x (w.getD i []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

theorem run_correct (g : BinaryGate) (x : ℕ → Bool) (w : List DNF) :
    value x (g.run w) =
      g.toGate.op.eval (g.toGate.inputs.map fun i => (w.map (value x)).getD i false) := by
  rcases g with ⟨b, l, r⟩
  cases b <;> simp only [BinaryGate.run, BinaryGate.toGate, Bool.false_eq_true, ↓reduceIte,
    value_meet, value_append, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.or_false, getD_map_value]

def simulate (gs : List BinaryGate) (w : List DNF) : List DNF :=
  match gs with
  | [] => w
  | g :: more => simulate more (w ++ [g.run w])

theorem simulate_correct (gs : List BinaryGate) (x : ℕ → Bool) (w : List DNF) :
    (simulate gs w).map (value x) =
      (gs.map BinaryGate.toGate).foldl
        (fun v (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
        (w.map (value x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [simulate, List.map_cons, List.foldl_cons, ih, List.map_append, List.map_nil,
      run_correct]

def inputs (n : ℕ) : List DNF := List.ofFn (fun i : Fin n => [[i.val]])

def extend {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then x ⟨i, h⟩ else false

theorem map_inputs {n : ℕ} (x : Fin n → Bool) :
    (inputs n).map (value (extend x)) = List.ofFn x := by
  simp [inputs, List.map_ofFn, value, extend, Function.comp_def]

def circuit (gs : List BinaryGate) (o : ℕ) : Circuit := ⟨gs.map BinaryGate.toGate, o⟩

theorem circuit_mono (gs : List BinaryGate) (o : ℕ) : Monotone2 (circuit gs o) := by
  intro g hg
  obtain ⟨⟨b, l, r⟩, _, rfl⟩ := List.mem_map.mp hg
  cases b <;> simp [BinaryGate.toGate]

theorem circuit_value (gs : List BinaryGate) (o n : ℕ) (x : Fin n → Bool) :
    (circuit gs o).eval (List.ofFn x) = value (extend x) ((simulate gs (inputs n)).getD o []) := by
  unfold Circuit.eval Circuit.wires circuit
  rw [← map_inputs x, ← simulate_correct, getD_map_value]

def edgeDNF (es : List (ℕ × ℕ)) : DNF := es.map (fun e => [e.1, e.2])

theorem edge_correct {n : ℕ} (x : Fin n → Bool) (es : List (ℕ × ℕ)) :
    value (extend x) (edgeDNF es) = true ↔
      ∃ u v : Fin n, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  simp only [value, edgeDNF, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨t, ⟨⟨u, v⟩, huv, rfl⟩, h⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    obtain ⟨hu, hv⟩ := h
    by_cases h₁ : u < n <;> simp [extend, h₁] at hu
    by_cases h₂ : v < n <;> simp [extend, h₂] at hv
    exact ⟨⟨u, h₁⟩, ⟨v, h₂⟩, huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨[u.val, v.val], ⟨(u.val, v.val), huv, rfl⟩, by simp [extend, hu, hv]⟩

def gates : List BinaryGate := [
  ⟨false, 2, 3⟩,
  ⟨false, 5, 11⟩,
  ⟨false, 24, 25⟩,
  ⟨true, 26, 13⟩,
  ⟨false, 3, 4⟩,
  ⟨false, 6, 12⟩,
  ⟨false, 28, 29⟩,
  ⟨true, 30, 14⟩,
  ⟨false, 0, 4⟩,
  ⟨false, 5, 7⟩,
  ⟨false, 32, 33⟩,
  ⟨true, 34, 15⟩,
  ⟨false, 1, 5⟩,
  ⟨false, 6, 8⟩,
  ⟨false, 36, 37⟩,
  ⟨true, 38, 16⟩,
  ⟨false, 2, 6⟩,
  ⟨false, 7, 9⟩,
  ⟨false, 40, 41⟩,
  ⟨true, 42, 17⟩,
  ⟨false, 3, 7⟩,
  ⟨false, 8, 10⟩,
  ⟨false, 44, 45⟩,
  ⟨true, 46, 18⟩,
  ⟨false, 4, 8⟩,
  ⟨false, 9, 11⟩,
  ⟨false, 48, 49⟩,
  ⟨true, 50, 19⟩,
  ⟨false, 5, 9⟩,
  ⟨false, 10, 12⟩,
  ⟨false, 52, 53⟩,
  ⟨true, 54, 20⟩,
  ⟨false, 0, 6⟩,
  ⟨false, 10, 11⟩,
  ⟨false, 56, 57⟩,
  ⟨true, 58, 21⟩,
  ⟨false, 1, 7⟩,
  ⟨false, 11, 12⟩,
  ⟨false, 60, 61⟩,
  ⟨true, 62, 22⟩,
  ⟨false, 0, 2⟩,
  ⟨false, 8, 12⟩,
  ⟨false, 64, 65⟩,
  ⟨true, 66, 23⟩,
  ⟨false, 27, 31⟩,
  ⟨false, 35, 39⟩,
  ⟨false, 43, 47⟩,
  ⟨false, 51, 55⟩,
  ⟨false, 59, 63⟩,
  ⟨false, 68, 69⟩,
  ⟨false, 70, 71⟩,
  ⟨false, 72, 67⟩,
  ⟨false, 73, 74⟩,
  ⟨false, 76, 75⟩]

def edges : List (ℕ × ℕ) := [(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem verification :
    let d := (simulate gates (inputs 24)).getD 77 []
    covers d (edgeDNF edges) = true ∧ covers (edgeDNF edges) d = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_9791_control54

open PEqualNP.Outside.L_meta_9791_control54 in
theorem PEqualNP.Outside.L_meta_9791_control54 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 54 ∧ (∀ x : Fin 24 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 24, (u.val, v.val) ∈ ([(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit gates 77, circuit_mono _ _, by decide, ?_⟩
  intro x
  rw [circuit_value]
  exact (Iff.intro (covers_sound verification.1 _) (covers_sound verification.2 _)).trans
    (edge_correct x edges)
