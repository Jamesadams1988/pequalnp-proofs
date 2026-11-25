import SignedFrontier

/-! Zero-slack signed frontier runs build a binary expression over individual
entries of the initial wire list. An accepted run uses every entry exactly once. -/
namespace Row12096Signed.SemanticCuts
open Row12096Signed

inductive Op where
  | both | either | leftOnly | rightOnly

def Op.apply : Op → W → W → W
  | .both, a, b => a &&& b
  | .either, a, b => a ||| b
  | .leftOnly, a, b => a &&& ~~~b
  | .rightOnly, a, b => b &&& ~~~a

inductive Tree (α : Type) where
  | leaf (label : α)
  | gate (op : Op) (left right : Tree α)

def Tree.leaves {α : Type} : Tree α → List α
  | .leaf i => [i]
  | .gate _ a b => a.leaves ++ b.leaves

def Tree.value {α : Type} (v : α → W) : Tree α → W
  | .leaf i => v i
  | .gate op a b => op.apply (a.value v) (b.value v)

theorem leavesNonempty {α : Type} (t : Tree α) : t.leaves ≠ [] := by
  induction t with
  | leaf => simp [Tree.leaves]
  | gate o a b ha hb => simp [Tree.leaves, ha]

private theorem singlesMap {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a, r) => (f a, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [singles, ih, List.map_map, Function.comp_def]

private theorem pairsMap {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [pairs, singlesMap, ih, List.map_map, Function.comp_def]

private theorem singlesPerm {α : Type} {ws : List α} {a : α} {r : List α}
    (h : (a,r) ∈ singles ws) : ws.Perm (a :: r) := by
  induction ws generalizing r with
  | nil => simp [singles] at h
  | cons x xs ih =>
    simp only [singles, List.mem_cons, List.mem_map] at h
    rcases h with eq | ⟨⟨y,ys⟩, hy, eq⟩
    · cases eq; exact .refl _
    · cases eq; exact ((ih hy).cons x).trans (.swap _ _ _)

private theorem pairsPerm {α : Type} {ws : List α} {a b : α} {r : List α}
    (h : (a,b,r) ∈ pairs ws) : ws.Perm (a :: b :: r) := by
  induction ws generalizing r with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    simp only [pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨y,ys⟩, hy, eq⟩ | ⟨⟨y,z,ys⟩, hy, eq⟩
    · cases eq; exact (singlesPerm hy).cons _
    · cases eq; exact ((ih hy).cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

private theorem singleTree {α : Type} {v : α → W} {forest : List (Tree α)} {g : W}
    (h : forest.map (Tree.value v) = [g]) :
    ∃ t : Tree α, t.value v = g ∧ t.leaves.Perm (forest.flatMap Tree.leaves) := by
  cases forest with
  | nil => simp at h
  | cons a r =>
    cases r with
    | nil => exact ⟨a, by simpa using h, by simp⟩
    | cons b rest => simp at h

private theorem classify {a b z : W} (h : z ∈ ops a b) : ∃ o : Op, o.apply a b = z := by
  simp [ops] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨.both,rfl⟩
  · exact ⟨.either,rfl⟩
  · exact ⟨.leftOnly,rfl⟩
  · exact ⟨.rightOnly,rfl⟩

/-- Lifting pair choices through the tree forest covers equal wire values at distinct positions. -/
theorem forestReadOnce {α : Type} (v : α → W) (k : ℕ) (forest : List (Tree α))
    (hit : optimized k 0 (forest.map (Tree.value v)) = true) :
    ∃ t : Tree α, (t.value v = goal ∨ t.value v = ~~~goal) ∧
      t.leaves.Perm (forest.flatMap Tree.leaves) := by
  have finish {g : W} (hg : g = goal ∨ g = ~~~goal) {f : List (Tree α)}
      (h : f.map (Tree.value v) = [g]) : ∃ t : Tree α,
      (t.value v = goal ∨ t.value v = ~~~goal) ∧ t.leaves.Perm (f.flatMap Tree.leaves) := by
    obtain ⟨t, ht, hp⟩ := singleTree h
    exact ⟨t, ht ▸ hg, hp⟩
  induction k generalizing forest with
  | zero =>
    simp only [optimized, Bool.or_eq_true, beq_iff_eq] at hit
    exact hit.elim (finish (.inl rfl)) (finish (.inr rfl))
  | succ k ih =>
    simp only [optimized, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hit
    rcases hit with single | ⟨⟨a,b,r⟩, hp, step⟩
    · exact single.elim (finish (.inl rfl)) (finish (.inr rfl))
    · rw [pairsMap] at hp
      obtain ⟨⟨u,vv,rest⟩, hmem, eq⟩ := List.mem_map.mp hp
      cases eq
      simp [dispatch, List.any_eq_true] at step
      obtain ⟨z, hz, _, tail⟩ := step
      obtain ⟨op, rfl⟩ := classify hz
      let next := Tree.gate op u vv :: rest
      obtain ⟨t, hvalue, hleaves⟩ := ih next (by exact tail)
      refine ⟨t, hvalue, hleaves.trans ?_⟩
      have perm := (pairsPerm hmem).symm.flatMap_right Tree.leaves
      simpa [next, Tree.leaves, List.append_assoc] using perm

/-- A read-once expression over the original positions, with no distinctness assumption on words. -/
theorem readOnce (ws : List W) (k : ℕ) (hit : optimized k 0 ws = true) :
    ∃ t : Tree (Fin ws.length), (t.value (fun i => ws[i.val]) = goal ∨
      t.value (fun i => ws[i.val]) = ~~~goal) ∧ t.leaves.Perm (List.finRange ws.length) := by
  let v (i : Fin ws.length) := ws[i.val]
  let f : List (Tree (Fin ws.length)) := (List.finRange ws.length).map Tree.leaf
  have vals : f.map (Tree.value v) = ws := by
    simp [f, v, Function.comp_def, Tree.value, List.finRange, List.map_ofFn]
  obtain ⟨t, h, perm⟩ := forestReadOnce v k f (by simpa only [vals] using hit)
  refine ⟨t, h, ?_⟩
  simpa [f, List.flatMap_map, Function.comp_def, Tree.leaves] using perm

/-- Agreement on the wire positions in ws suffices to determine u at a packed row. -/
def depends (ws : List W) (u : W) : Prop :=
  ∀ i j : Fin 256, (∀ w ∈ ws, w[i.val] = w[j.val]) → u[i.val] = u[j.val]

private theorem dependsNot {ws : List W} {u : W} (h : depends ws u) : depends ws (~~~u) := by
  intro i j eq
  simp only [BitVec.getElem_not, h i j eq]

theorem treeDepends {α : Type} (v : α → W) (t : Tree α) :
    depends (t.leaves.map v) (t.value v) := by
  induction t with
  | leaf a =>
    intro i j h
    exact h (v a) (by simp [Tree.leaves])
  | gate op a b ha hb =>
    intro i j h
    have aeq := ha i j (fun w hw => h w (by simp [Tree.leaves, hw]))
    have beq := hb i j (fun w hw => h w (by simp [Tree.leaves, hw]))
    cases op <;> simp only [Tree.value, Op.apply, BitVec.getElem_and, BitVec.getElem_or,
      BitVec.getElem_not, aeq, beq]

/-- The last gate separates the raw input positions into two nonempty disjoint parts.
Complements of its children absorb every signed operation and output polarity. -/
theorem lastSplit (ws : List W) (k : ℕ) (len : 2 ≤ ws.length) (hit : optimized k 0 ws = true) :
    ∃ A B : List W, A ≠ [] ∧ B ≠ [] ∧ (A ++ B).Perm ws ∧
      ∃ g u v : W, (g = goal ∨ g = ~~~goal) ∧ g = u &&& v ∧ depends A u ∧ depends B v := by
  let raw (i : Fin ws.length) := ws[i.val]
  obtain ⟨t, ht, perm⟩ := readOnce ws k hit
  cases t with
  | leaf i =>
    have length := perm.length_eq
    simp [Tree.leaves] at length
    omega
  | gate op a b =>
    let A := a.leaves.map raw
    let B := b.leaves.map raw
    have hp : (A ++ B).Perm ws := by
      have p := perm.map raw
      simpa [A, B, Tree.leaves, raw, List.finRange, List.map_ofFn, Function.comp_def, List.ofFn_getElem] using p
    refine ⟨A, B, by simpa [A] using leavesNonempty a, by simpa [B] using leavesNonempty b, hp, ?_⟩
    let x := a.value raw
    let y := b.value raw
    have hx : depends A x := treeDepends raw a
    have hy : depends B y := treeDepends raw b
    change op.apply x y = goal ∨ op.apply x y = ~~~goal at ht
    cases op with
    | both => exact ⟨_, x, y, ht, rfl, hx, hy⟩
    | either =>
      have neg : ~~~(x ||| y) = goal ∨ ~~~(x ||| y) = ~~~goal := by
        rcases ht with h | h
        · exact .inr (congrArg (~~~·) h)
        · exact .inl ((congrArg (~~~·) h).trans BitVec.not_not)
      exact ⟨_, ~~~x, ~~~y, neg, BitVec.not_or, dependsNot hx, dependsNot hy⟩
    | leftOnly => exact ⟨_, x, ~~~y, ht, rfl, hx, dependsNot hy⟩
    | rightOnly => exact ⟨_, ~~~x, y, ht, BitVec.and_comm _ _, dependsNot hx, hy⟩

#print axioms lastSplit
end Row12096Signed.SemanticCuts
