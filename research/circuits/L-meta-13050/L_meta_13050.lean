import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13050

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The support argument below adapts L_meta_757.lean by KainanP (commit
-- 073fb082aa04ea681e8529ca9f5bc67580e5ad4a, Apache-2.0). It charges NOT gates
-- zero and counts only the first input that their Boolean semantics reads.
-- The upstream support bound was adapted from the project's MetaComplexity/Helpers/Support.lean,
-- with the evaluation fold and admissible gates defined here for the allowed imports.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private def used (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private def charge (g : Gate) : ℕ :=
  match g.op with
  | .not => 0
  | _ => 1

private theorem effective_value (g : Gate) (w : List Bool) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
    g.op.eval ((used g).map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> rfl

private theorem charged_length (g : Gate) (hg : g.inputs.length ≤ 2) :
    (used g).length ≤ charge g + 1 := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [used,charge]

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  ((used g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ used g, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      rw [effective_value g w,effective_value g w']
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + charge g) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (used g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (used g).toFinset).card ≤ (W.card - 1) + (charge g + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (charged_length g hg)) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (used g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

private def binaryBudget (gs : List Gate) := (gs.map charge).sum

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + binaryBudget gs) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; simpa [binaryBudget,suppsFrom] using h
  | cons g gs ih =>
    intro t L hok h
    have step := ih (t + charge g) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    simpa only [binaryBudget,List.map_cons,List.sum_cons,Nat.add_assoc,suppsFrom,List.foldl_cons] using step

private theorem budget_le (gs : List Gate) : binaryBudget gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryBudget]
  | cons g gs ih =>
    have c : charge g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [charge]
    change charge g + binaryBudget gs ≤ gs.length + 1
    omega

private theorem budget_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) :
    binaryBudget gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨k,mem,eq⟩ := h
    rcases List.mem_cons.mp mem with rfl | tail
    · have c : charge k = 0 := by simp [charge,eq]
      have := budget_le gs
      change charge k + binaryBudget gs < gs.length+1
      omega
    · have := ih ⟨k,tail,eq⟩
      have c : charge g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [charge]
      change charge g + binaryBudget gs < gs.length+1
      omega

/-- A NOT in a fan-in-two circuit computing a function essential in n inputs forces at least n gates. -/
theorem lower_with_not (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (C : Circuit) (ok : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hn : ∃ g ∈ C.gates, g.op = .not) : n ≤ C.size := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  have := budget_lt hn
  change n ≤ C.gates.length
  omega

/-- An n-gate monotone realization suffices to eliminate NOT without a size penalty on an n-essential function. -/
theorem replace_at_n (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (W : Circuit) (mono : Monotone2 W) (size : W.size ≤ n)
    (val : ∀ x : Fin n → Bool, W.eval (List.ofFn x) = f x)
    (s : ℕ) (h : HasCircuitSize n f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨C,ok,hs,hval⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · exact ⟨W,mono,le_trans size (le_trans (lower_with_not n f hdep C ok hval hn) hs),val⟩
  · refine ⟨C,?_,hs,hval⟩
    intro g hg
    obtain ⟨hop,hlen⟩ := ok g hg
    refine ⟨?_,hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn ⟨g,hg,h⟩)

def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277074666 * 2 ^ 32 + 4277074602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def sample (bits : ℕ) (i : Fin 6) : Bool := bits.testBit i.val

private theorem all_essential : ∀ i : Fin 6, ∃ x, table (Function.update x i (!x i)) ≠ table x := by
  intro i
  fin_cases i
  · exact ⟨sample 0, by decide⟩
  · exact ⟨sample 16, by decide⟩
  · exact ⟨sample 8, by decide⟩
  · exact ⟨sample 4, by decide⟩
  · exact ⟨sample 2, by decide⟩
  · exact ⟨sample 6, by decide⟩

def sixGates : Circuit :=
  ⟨[⟨.and,[2,5]⟩,⟨.or,[4,6]⟩,⟨.and,[1,7]⟩,⟨.and,[2,3]⟩,⟨.or,[8,9]⟩,⟨.or,[0,10]⟩],11⟩

end PEqualNP.Outside.L_meta_13050

open PEqualNP.Outside.L_meta_13050 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
/-- Refutation of the assigned negative proposition, using a six-gate witness. -/
theorem PEqualNP.Outside.L_meta_13050 : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4277074602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4277074602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro neg
  apply neg
  intro s hs
  exact replace_at_n 6 table all_essential sixGates (by simp [Monotone2,sixGates])
    (by decide) (by decide +kernel) s hs
