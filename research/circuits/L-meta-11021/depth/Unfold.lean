import TreeBase

/-! Unfold each queried wire against the prefix available *at its evaluation*.
An invalid read is represented by an invalid leaf, of depth and cost zero. -/
namespace DepthSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def nextDepth (D : List ℕ) (g : Gate) :=
  (g.inputs.map fun i => D.getD i 0).foldr max 0 + 1

private def nextValue (w : List Bool) (g : Gate) :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def Models {n} (D : List ℕ) (w : (Fin n → Bool) → List Bool) : Prop :=
  ∀ i, ∃ t : Tree n, t.Good ∧ t.cost + 1 ≤ 2 ^ (D.getD i 0) ∧
    ∀ x, t.eval x = (w x).getD i false

private theorem newGate {n} {D : List ℕ} {w : (Fin n → Bool) → List Bool}
    (hw : Models D w) (g : Gate)
    (hg : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ t : Tree n, t.Good ∧ t.cost + 1 ≤ 2 ^ nextDepth D g ∧
      ∀ x, t.eval x = nextValue (w x) g := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    exact ⟨.node op (.leaf n) (.leaf n) 0, ⟨hop, trivial, trivial⟩, by change 2 ≤ 2; decide, fun _ => rfl⟩
  | cons i tail =>
    obtain ⟨a, ha, hca, hwa⟩ := hw i
    cases tail with
    | nil =>
      refine ⟨.node op a (.leaf n) 1, ⟨hop, ha, trivial⟩, ?_, ?_⟩
      · simp only [Tree.cost, nextDepth, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, Nat.max_zero, pow_succ, Nat.add_zero]
        omega
      · intro x
        simp [Tree.eval, nextValue, hwa]
    | cons j rest =>
      cases rest with
      | cons k tail => simp at hlen
      | nil =>
        obtain ⟨b, hb, hcb, hwb⟩ := hw j
        refine ⟨.node op a b 2, ⟨hop, ha, hb⟩, ?_, ?_⟩
        · simp only [nextDepth, Tree.cost, List.map_cons, List.map_nil,
            List.foldr_cons, List.foldr_nil, Nat.max_zero, pow_succ]
          have h1 : 2 ^ D.getD i 0 ≤ 2 ^ max (D.getD i 0) (D.getD j 0) :=
            Nat.pow_le_pow_right (by decide) (le_max_left _ _)
          have h2 : 2 ^ D.getD j 0 ≤ 2 ^ max (D.getD i 0) (D.getD j 0) :=
            Nat.pow_le_pow_right (by decide) (le_max_right _ _)
          omega
        · intro x
          simp [Tree.eval, nextValue, hwa, hwb]

private theorem snoc_same {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

private theorem snoc_other {α : Type} (l : List α) (a d : α) (i : ℕ)
    (h : i ≠ l.length) : (l ++ [a]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · have hbig : (l ++ [a]).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hbig, List.getD_eq_default _ _ (by omega)]

private theorem foldModels {n} (gs : List Gate) (D : List ℕ) (w : (Fin n → Bool) → List Bool)
    (hlen : ∀ x, (w x).length = D.length) (hw : Models D w)
    (hg : ∀ g ∈ gs, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Models (gs.foldl (fun d g => d ++ [nextDepth d g]) D)
      (fun x => gs.foldl (fun z g => z ++ [nextValue z g]) (w x)) := by
  induction gs generalizing D w with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro x
      simp [hlen x]
    · intro i
      by_cases heq : i = D.length
      · subst i
        obtain ⟨t, ht, hcost, hval⟩ := newGate hw g (hg g List.mem_cons_self)
        refine ⟨t, ht, by simpa [snoc_same] using hcost, ?_⟩
        intro x
        rw [← hlen x, snoc_same]
        exact hval x
      · obtain ⟨t, ht, hcost, hval⟩ := hw i
        refine ⟨t, ht, by rwa [snoc_other _ _ _ _ heq], ?_⟩
        intro x
        rw [snoc_other _ _ _ _ (by rwa [hlen x])]
        exact hval x
    · exact fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')

/-- A depth-`d` circuit unfolds to a tree containing at most `2^d−1` gates. -/
theorem exists_tree (C : Circuit) (n : ℕ) (hC : FanInTwo C) :
    ∃ t : Tree n, t.Good ∧ t.cost + 1 ≤ 2 ^ C.depth n ∧ t.eval = circuitFun n C := by
  have inputs : Models (List.replicate n 0) (fun x : Fin n → Bool => List.ofFn x) := by
    intro i
    refine ⟨.leaf i, trivial, ?_, fun _ => rfl⟩
    exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨t, ht, hcost, hval⟩ :=
    foldModels C.gates _ _ (fun x => by simp) inputs hC C.output
  exact ⟨t, ht, hcost, funext hval⟩

end DepthSize
