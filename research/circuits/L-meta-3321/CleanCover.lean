import PEqualNP.Defs

/-!
A vertex-cover circuit with a witness for every AND.  The edge decomposition and size
accounting follow the project's Helpers.EdgeUpperMono.  The segment certificate also tracks
backward reads and the semantics of all intermediate AND wires through concatenation.
-/
namespace CleanCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

private abbrev inp {n : ℕ} (w : List Bool) : Fin n → Bool := fun i => w.getD i false

private def Good (P : Prop) (m : ℕ) (gs : List Gate) (w : List Bool) : Prop :=
  ∀ j (hj : j < gs.length),
    (gs[j].op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gs[j].inputs.length ≤ 2) ∧
    (∀ i ∈ gs[j].inputs, i < m + j) ∧
    (gs[j].op = GateOp.and → (wiresFrom gs w).getD (m+j) false = true → P)

private theorem good_append {P : Prop} {m : ℕ} {as bs : List Gate} {w : List Bool}
    (hw : w.length = m) (ha : Good P m as w)
    (hb : Good P (m+as.length) bs (wiresFrom as w)) :
    Good P m (as ++ bs) w := by
  intro j hj
  by_cases h : j < as.length
  · simp only [List.getElem_append_left h]
    obtain ⟨ok, back, clean⟩ := ha j h
    refine ⟨ok, back, fun hand he => clean hand ?_⟩
    rw [wiresFrom_append, getD_wiresFrom] at he
    · exact he
    · rw [length_wiresFrom, hw]; omega
  · have h' : j - as.length < bs.length := by simp only [List.length_append] at hj; omega
    simp only [List.getElem_append_right (Nat.le_of_not_gt h)]
    have index : m + as.length + (j-as.length) = m+j := by omega
    obtain ⟨ok, back, clean⟩ := hb (j-as.length) h'
    rw [index] at back clean
    exact ⟨ok, back, by rw [wiresFrom_append]; exact clean⟩

private def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), gs.length ≤ s ∧ out < m + gs.length ∧
    ∀ w : List Bool, w.length = m →
      Good (P (inp w)) m gs w ∧ (wiresFrom gs w).getD out false = F (inp w)

private theorem bld_mono {n : ℕ} {P F} {s s' : ℕ} (h : Bld n P F s) (hs : s ≤ s') :
    Bld n P F s' := by
  intro m hm
  obtain ⟨gs, o, len, ho, ev⟩ := h m hm
  exact ⟨gs, o, le_trans len hs, ho, ev⟩

private theorem bld_congr {n : ℕ} {P F H} {s : ℕ} (h : Bld n P F s)
    (e : ∀ x, F x = H x) : Bld n P H s := by
  exact (funext e) ▸ h

private theorem bld_var {n : ℕ} {P} (i : Fin n) : Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp; omega, fun w _ => ⟨?_, rfl⟩⟩
  intro j hj; simp at hj

private theorem bld_bin {n : ℕ} {P F H} {s1 s2 : ℕ} (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (f : Bool → Bool → Bool) (hf : ∀ a b, op.eval [a,b] = f a b)
    (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (safe : op = GateOp.and → ∀ x, f (F x) (H x) = true → P x) :
    Bld n P (fun x => f (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨as, a, la, ha, eva⟩ := h1 m hm
  obtain ⟨bs, b, lb, hb, evb⟩ := h2 (m+as.length) (by omega)
  let g : Gate := ⟨op, [a,b]⟩
  let M := m + (as++bs).length
  refine ⟨as ++ bs ++ [g], M, by simp; omega, by simp [M], ?_⟩
  intro w hw
  let v := wiresFrom as w
  let u := wiresFrom (as++bs) w
  have lv : v.length = m+as.length := by simp [v, length_wiresFrom, hw]
  have lu : u.length = M := by simp [u, M, length_wiresFrom, hw]
  obtain ⟨ga, ea⟩ := eva w hw
  obtain ⟨gb, eb⟩ := evb v lv
  have hi : @inp n v = inp w := by
    funext i
    exact getD_wiresFrom as w i (by have := i.isLt; omega)
  rw [hi] at gb eb
  have ga' := good_append hw ga gb
  have wa : u.getD a false = F (inp w) := by
    change (wiresFrom (as++bs) w).getD a false = _
    rw [wiresFrom_append, getD_wiresFrom, ea]
    rw [length_wiresFrom, hw]; exact ha
  have wb : u.getD b false = H (inp w) := by
    change (wiresFrom (as++bs) w).getD b false = _
    rw [wiresFrom_append]; exact eb
  have last : (wiresFrom [g] u).getD M false = f (F (inp w)) (H (inp w)) := by
    change (u ++ [op.eval ([a,b].map (fun k => u.getD k false))]).getD M false = _
    rw [← lu]
    have snoc (val : Bool) : (u ++ [val]).getD u.length false = val := by simp
    rw [snoc]
    simp only [List.map_cons, List.map_nil, hf, wa, wb]
  constructor
  · apply good_append hw ga'
    intro j hj
    have : j = 0 := by simpa using hj
    subst j
    simp only [List.getElem_cons_zero, Nat.add_zero]
    refine ⟨?_, ?_, fun hand he => safe hand (inp w) (last ▸ he)⟩
    · rcases hop with h | h <;> simp [g,h]
    · intro i h
      simp only [g,List.mem_cons,List.not_mem_nil,or_false] at h
      simp only [List.length_append]
      rcases h with rfl | rfl <;> omega
  · rw [wiresFrom_append]
    exact last

private theorem bld_or {n : ℕ} {P F H} {s1 s2} (h1 : Bld n P F s1) (h2 : Bld n P H s2) :
    Bld n P (fun x => F x || H x) (s1+s2+1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2 (by simp)

private theorem bld_and {n : ℕ} {P F H} {s1 s2} (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (h : ∀ x, (F x && H x) = true → P x) :
    Bld n P (fun x => F x && H x) (s1+s2+1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2 (fun _ => h)

/-- The OR of the inputs in a nonempty list. -/
private theorem bld_anyList {n : ℕ} {P : (Fin n → Bool) → Prop} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

/-- The OR of the inputs in a nonempty finset `S`, with `|S| - 1` gates. -/
private theorem bld_anyFinset {n : ℕ} {P : (Fin n → Bool) → Prop} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
/-- The edge function of a nonempty set of edges `E` with a cover `T`. -/
private theorem bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    (∀ x : Fin n → Bool, (∃ e ∈ E, ∀ v ∈ e, x v = true) → P x) →
    Bld n P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc hP
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hP
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    -- the star at `t`
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have guard : ∀ x : Fin n → Bool,
          (x t && decide (∃ v ∈ S, x v = true)) = true → P x := by
        intro x hx
        rw [Bool.and_eq_true, decide_eq_true_iff] at hx
        obtain ⟨ht, v, hv, hvx⟩ := hx
        have he1 : s(t, v) ∈ E1 := (Finset.mem_filter.1 hv).2
        refine hP x ⟨s(t,v), (Finset.mem_filter.1 he1).1, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      have := bld_and (bld_var t) (bld_anyFinset S hSne) guard
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    have recGuard : ∀ x : Fin n → Bool, (∃ e ∈ E2, ∀ v ∈ e, x v = true) → P x := by
      rintro x ⟨e, he, hx⟩
      exact hP x ⟨e, (Finset.mem_filter.1 he).1, hx⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2 recGuard)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2 recGuard) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

private theorem bld_circuit {n : ℕ} {P F} {s : ℕ} (h : Bld n P F s) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ circuitFun n D = F ∧ D.size ≤ s ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n+j) false = true → P x := by
  obtain ⟨gs, out, len, _, ev⟩ := h n le_rfl
  let D : Circuit := ⟨gs,out⟩
  have at_eq (j : ℕ) (hj : j < gs.length) : gateAt D j = gs[j] := by
    simp [D,gateAt,List.getD_eq_getElem?_getD,hj]
  have ev' (x : Fin n → Bool) :
      Good (P x) n gs (List.ofFn x) ∧ (wiresFrom gs (List.ofFn x)).getD out false = F x := by
    have key : inp (List.ofFn x) = x := by funext i; simp [inp]
    simpa only [key] using ev (List.ofFn x) (by simp)
  have static := (ev' fun _ => false).1
  refine ⟨D, ?_, ?_, ?_, len, ?_⟩
  · intro g hg
    obtain ⟨j,hj,hg'⟩ := List.mem_iff_getElem.1 hg
    exact hg' ▸ (static j hj).1
  · intro j hj
    rw [at_eq j hj]; exact (static j hj).2.1
  · funext x
    exact (ev' x).2
  · intro j hj ho x
    rw [at_eq j hj] at ho
    exact ((ev' x).1 j hj).2.2 ho

/-- A cover computes the edge function with one AND per nonempty star. Every true AND
already witnesses an edge of the graph, and every gate reads only earlier wires. -/
theorem edge_upper_clean (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hne : ∃ i j : Fin n, G.Adj i j)
    (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n+j) false = true →
        ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true := by
  classical
  obtain ⟨i0, j0, h0⟩ := hne
  have hne' : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  have edge (x : Fin n → Bool) : (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
      ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true := by
    constructor
    · rintro ⟨e, he, h⟩
      revert he h
      refine Sym2.ind (fun a b => ?_) e
      intro he h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a,b,he,h a (Sym2.mem_mk_left _ _),h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨a,b,h,ha,hb⟩
      refine ⟨s(a,b), by simpa using h, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
  obtain ⟨D,mono,back,ev,size,guard⟩ := bld_circuit
    (bld_edges n _ T G.edgeFinset hne' cov fun x => (edge x).1)
  refine ⟨D,mono,back,?_,by have := hne'.card_pos; omega,guard⟩
  rw [ev]; funext x
  exact decide_eq_decide.mpr (edge x)

end CleanCover
