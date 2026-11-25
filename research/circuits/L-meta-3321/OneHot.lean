import PEqualNP.Defs

/-!
For each wire, collect the input indices that reach it through OR gates alone.
An AND contributes the empty set to this propagation. Such a gate passes the
local test if the intersection of its operands' OR supports is empty. The
whole test is equivalent to every AND being false on every single-input
assignment. This includes gates of arity zero or one.
-/
namespace PEqualNP.Outside.L_meta_3321_OneHot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def gateBit (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def finish (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [gateBit g v]) w

theorem finish_keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (finish gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (finish gs (w ++ [gateBit g w])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

/-- Semantic one-hot condition for a single valuation of the starting wires. -/
def Quiet (gs : List Gate) (w : List Bool) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].op = .and →
    (finish gs w).getD (w.length + j) false = false

theorem quiet_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    Quiet (g :: gs) w ↔
    (g.op = .and → gateBit g w = false) ∧ Quiet gs (w ++ [gateBit g w]) := by
  let v := w ++ [gateBit g w]
  have hlen : v.length = w.length + 1 := by simp [v]
  have first : (finish (g :: gs) w).getD w.length false = gateBit g w := by
    change (finish gs v).getD w.length false = _
    rw [finish_keep _ _ _ (by omega)]
    simp [v]
  constructor
  · intro h
    refine ⟨fun hop => ?_, ?_⟩
    · have hz := h 0 (by simp) hop
      simpa only [Nat.add_zero, first] using hz
    · intro j hj hop
      have hz := h (j + 1) (by simpa using hj) hop
      change (finish gs v).getD (v.length + j) false = false
      rw [show v.length + j = w.length + (j + 1) by omega]
      exact hz
  · rintro ⟨h0, hmore⟩ j hj hop
    cases j with
    | zero => simpa only [Nat.add_zero, first] using h0 hop
    | succ j =>
      have hz := hmore j (by simpa using hj) hop
      change (finish gs v).getD (v.length + j) false = false at hz
      change (finish gs v).getD (w.length + (j + 1)) false = false
      simpa only [hlen, Nat.add_right_comm, Nat.add_comm 1 j, Nat.add_assoc] using hz

abbrev Support (n : ℕ) := Finset (Fin n)

def containsInput {n : ℕ} (t : Fin n) (s : Support n) : Bool := decide (t ∈ s)

theorem getD_contains {n : ℕ} (W : List (Support n)) (t : Fin n) (i : ℕ) :
    (W.map (containsInput t)).getD i false = containsInput t (W.getD i ∅) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

def orJoin {n : ℕ} (W : List (Support n)) (ins : List ℕ) : Support n :=
  ins.foldr (fun i acc => W.getD i ∅ ∪ acc) ∅

theorem mem_join {n : ℕ} (W : List (Support n)) (ins : List ℕ) (t : Fin n) :
    t ∈ orJoin W ins ↔ ∃ i ∈ ins, t ∈ W.getD i ∅ := by
  induction ins with
  | nil => simp [orJoin]
  | cons i ins ih => simp [orJoin] at ih ⊢; exact or_congr_right ih

def appendSupport {n : ℕ} (g : Gate) (W : List (Support n)) : Support n :=
  match g.op with
  | .or => orJoin W g.inputs
  | _ => ∅

def separated {n : ℕ} (ins : List ℕ) (W : List (Support n)) : Prop :=
  ∀ t : Fin n, ∃ i ∈ ins, t ∉ W.getD i ∅

theorem binary_separated {n : ℕ} (a b : ℕ) (W : List (Support n)) :
    separated [a,b] W ↔ Disjoint (W.getD a ∅) (W.getD b ∅) := by
  simp only [separated, List.mem_cons, List.not_mem_nil, or_false, Finset.disjoint_left]
  constructor
  · intro h t ha hb
    obtain ⟨i, rfl | rfl, no⟩ := h t
    · exact no ha
    · exact no hb
  · intro h t
    by_cases ha : t ∈ W.getD a ∅
    · exact ⟨b, Or.inr rfl, h ha⟩
    · exact ⟨a, Or.inl rfl, ha⟩

theorem and_zero {n : ℕ} (g : Gate) (ha : g.op = .and) (W : List (Support n)) :
    separated g.inputs W ↔ ∀ t, gateBit g (W.map (containsInput t)) = false := by
  simp only [gateBit, ha, GateOp.eval, List.all_map, Function.comp_def, id_eq, getD_contains]
  simp [separated, List.all_eq_false, containsInput]

theorem support_matches {n : ℕ} (g : Gate) (hAO : g.op = .and ∨ g.op = .or)
    (W : List (Support n)) (h : g.op = .and → separated g.inputs W) (t : Fin n) :
    containsInput t (appendSupport g W) = gateBit g (W.map (containsInput t)) := by
  rcases hAO with ha | ho
  · rw [(and_zero g ha W).mp (h ha) t]
    simp [appendSupport, ha, containsInput]
  · apply Bool.eq_iff_iff.mpr
    simp only [gateBit, ho, GateOp.eval, List.any_map, Function.comp_def, id_eq, getD_contains]
    simp [appendSupport, ho, containsInput, mem_join, List.any_eq_true]

def scan {n : ℕ} : List Gate → List (Support n) → Prop
  | [], _ => True
  | g :: gs, W =>
    (g.op = .and → separated g.inputs W) ∧ scan gs (W ++ [appendSupport g W])

/-- Executable certificate check. All AND gates write the empty support, regardless
of the outcome of the overlap test, so only OR gates propagate input indices. -/
def check {n : ℕ} : List Gate → List (Support n) → Bool
  | [], _ => true
  | g :: gs, W =>
    let ok := match g.op with
      | .and => decide (∀ t : Fin n, ∃ i ∈ g.inputs, t ∉ W.getD i ∅)
      | _ => true
    ok && check gs (W ++ [appendSupport g W])

theorem check_eq {n : ℕ} (gs : List Gate) (W : List (Support n)) :
    check gs W = true ↔ scan gs W := by
  induction gs generalizing W with
  | nil => simp [check, scan]
  | cons g gs ih =>
    cases g with
    | mk op ins =>
      cases op <;> simp [check, scan, separated, ih]

theorem scan_exact {n : ℕ} (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (W : List (Support n)) :
    scan gs W ↔ ∀ t : Fin n, Quiet gs (W.map (containsInput t)) := by
  induction gs generalizing W with
  | nil => simp [scan, Quiet]
  | cons g gs ih =>
    have hgate := hAO g List.mem_cons_self
    have hrest := fun k hk => hAO k (List.mem_cons_of_mem _ hk)
    have eq (localTest : g.op = .and → separated g.inputs W) (t : Fin n) :
        (W ++ [appendSupport g W]).map (containsInput t) =
          W.map (containsInput t) ++ [gateBit g (W.map (containsInput t))] := by
      simp [support_matches g hgate W localTest t]
    constructor
    · rintro ⟨h, more⟩ t
      apply (quiet_cons g gs _).mpr
      exact ⟨fun ha => (and_zero g ha W).mp (h ha) t, eq h t ▸ (ih hrest _).mp more t⟩
    · intro h
      have first (ha : g.op = .and) : separated g.inputs W :=
        (and_zero g ha W).mpr (fun t => ((quiet_cons g gs _).mp (h t)).1 ha)
      refine ⟨first, (ih hrest _).mpr (fun t => ?_)⟩
      rw [eq first t]
      exact ((quiet_cons g gs _).mp (h t)).2

def raw (n : ℕ) : List (Support n) := List.ofFn fun i : Fin n => {i}

theorem exact_one_hot (n : ℕ) (C : Circuit) (hAO : Monotone2 C) :
    scan C.gates (raw n) ↔ ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ t : Fin n,
      (C.wires (List.ofFn (fun i : Fin n => decide (i = t)))).getD (n + j) false = false := by
  have inputs (t : Fin n) : (raw n).map (containsInput t) =
      List.ofFn (fun i : Fin n => decide (i = t)) := by
    simp [raw, containsInput, List.map_ofFn, Function.comp_def, eq_comm]
  rw [scan_exact _ (fun g hg => (hAO g hg).1)]
  simp only [Quiet, inputs, List.length_ofFn]
  constructor
  · intro h j hj ha t
    exact h t j hj ((List.getD_eq_getElem _ _ hj) ▸ ha)
  · intro h t j hj ha
    apply h j hj _ t
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using ha

theorem bipartite_one_hot (N : ℕ) (C : Circuit) (hAO : Monotone2 C) :
    scan C.gates (raw (N+N)) ↔ ∀ j < C.gates.length, (gateAt C j).op = .and →
    (∀ p : Fin N, (C.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.castAdd N p)))).getD
      (N+N+j) false = false) ∧
    (∀ l : Fin N, (C.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.natAdd N l)))).getD
      (N+N+j) false = false) := by
  rw [exact_one_hot _ C hAO]
  constructor
  · intro h j hj ha
    exact ⟨fun p => h j hj ha _, fun l => h j hj ha _⟩
  · intro h j hj ha t
    exact Fin.addCases (h j hj ha).1 (h j hj ha).2 t

/-- A wire that individually forces an incident edge is clean and can never
fire on a singleton. The same criterion applies to wires lifted toward the output. -/
theorem edge_forcing {N : ℕ} (I : Fin N → Fin N → Prop)
    (w : (Fin (N+N) → Bool) → Bool)
    (forces : ∀ z, w z = true → ∃ p l : Fin N, I p l ∧
      z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (∀ z, w z = true →
      w (fun k : Fin (N+N) => decide (k.val < N) && z k) = true ∨
      w (fun k : Fin (N+N) => decide (N ≤ k.val) && z k) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    (∀ t : Fin (N+N), w (fun i => decide (i = t)) = false) := by
  refine ⟨fun z hz => Or.inr (Or.inr (forces z hz)), ?_⟩
  intro t
  cases e : w (fun i => decide (i = t)) with
  | false => rfl
  | true =>
    obtain ⟨p, l, _, hp, hl⟩ := forces _ e
    have eq : Fin.castAdd N p = Fin.natAdd N l := (of_decide_eq_true hp).trans (of_decide_eq_true hl).symm
    have vals := congrArg Fin.val eq
    simp at vals
    omega

end PEqualNP.Outside.L_meta_3321_OneHot
