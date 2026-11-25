import PEqualNP.Defs

/-! Exact minterm tests for the semantic cleanliness condition of L-meta-3321.
The wire-monotonicity induction adapts the project's LowMergeWires.lean. -/
namespace IncidenceMinterms
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (a : List Bool) (g : Gate) :=
  a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]

/-- Pointwise order on Bool lists read through `getD`. -/
private def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

private theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

private theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

/-- The value of an arbitrary wire. Unavailable wires receive the default false. -/
def wire {n : ℕ} (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem wire_monotone {n : ℕ} (C : Circuit) (h : Monotone2 C) (w : ℕ) :
    Monotone (wire (n:=n) C w) := by
  intro a b hab
  apply Bool.le_iff_imp.mpr
  apply fold_mono C.gates (fun g hg => (h g hg).1) (List.ofFn a) (List.ofFn b) (by simp)
  intro i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  split at hi
  · next h =>
    simp [h] at hi ⊢
    exact Bool.le_iff_imp.mp (hab ⟨i,h⟩) hi
  · simp_all

abbrev Input (n : ℕ) := Fin (n + n) → Bool

def points {n : ℕ} (z : Input n) : Input n := fun i => decide (i.val < n) && z i
def lines {n : ℕ} (z : Input n) : Input n := fun i => decide (n ≤ i.val) && z i

def hits {n : ℕ} (I : Fin n → Fin n → Prop) (z : Input n) : Prop :=
  ∃ p l : Fin n, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true

def Clean {n : ℕ} (I : Fin n → Fin n → Prop) (F : Input n → Bool) : Prop :=
  ∀ z, F z = true → F (points z) = true ∨ F (lines z) = true ∨ hits I z

private theorem points_le {n : ℕ} (z : Input n) : points z ≤ z := by
  intro i; apply Bool.le_iff_imp.mpr; simp [points]
private theorem lines_le {n : ℕ} (z : Input n) : lines z ≤ z := by
  intro i; apply Bool.le_iff_imp.mpr; simp [lines]
private theorem points_mono {n : ℕ} : Monotone (@points n) := by
  intro a b hab i
  apply Bool.le_iff_imp.mpr
  simp only [points, Bool.and_eq_true]
  exact fun h => ⟨h.1, Bool.le_iff_imp.mp (hab i) h.2⟩
private theorem lines_mono {n : ℕ} : Monotone (@lines n) := by
  intro a b hab i
  apply Bool.le_iff_imp.mpr
  simp only [lines, Bool.and_eq_true]
  exact fun h => ⟨h.1, Bool.le_iff_imp.mp (hab i) h.2⟩

/-- On an inclusion-minimal true input, a successful projection must preserve
the whole input. Checking the mixed minterms for an incident edge is sufficient. -/
theorem clean_iff_minterms {n : ℕ} (I : Fin n → Fin n → Prop)
    (F : Input n → Bool) (hF : Monotone F) :
    Clean I F ↔ ∀ z, Minimal (fun x => F x = true) z →
      points z = z ∨ lines z = z ∨ hits I z := by
  constructor
  · intro clean z hz
    rcases clean z hz.1 with hp | hl | he
    · exact Or.inl (le_antisymm (points_le z) (hz.2 hp (points_le z)))
    · exact Or.inr (Or.inl (le_antisymm (lines_le z) (hz.2 hl (lines_le z))))
    · exact Or.inr (Or.inr he)
  · intro h z hz
    obtain ⟨m, hmz, hm⟩ := exists_minimal_le_of_wellFoundedLT (fun x => F x = true) z hz
    rcases h m hm with hp | hl | ⟨p,l,he,hp,hl⟩
    · exact Or.inl (Bool.le_iff_imp.mp (hF (points_mono hmz)) (hp.symm ▸ hm.1))
    · exact Or.inr (Or.inl (Bool.le_iff_imp.mp (hF (lines_mono hmz)) (hl.symm ▸ hm.1)))
    · exact Or.inr (Or.inr ⟨p,l,he,Bool.le_iff_imp.mp (hmz _) hp,Bool.le_iff_imp.mp (hmz _) hl⟩)

/-- The minterm test needs only immediate one-bit deletions. -/
theorem minimal_iff_deletions {k : ℕ} (F : (Fin k → Bool) → Bool) (mono : Monotone F)
    (z : Fin k → Bool) : Minimal (fun x => F x = true) z ↔
    F z = true ∧ ∀ i, z i = true → F (Function.update z i false) = false := by
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hf
    have leq : Function.update z i false ≤ z := by
      intro j
      by_cases he : j = i
      · subst j; simp
      · simp [Function.update_of_ne he]
    have b := Bool.le_iff_imp.mp (hm.2 hf leq i) hi
    simp at b
  · rintro ⟨ht, hj⟩
    refine ⟨ht, ?_⟩
    intro y hy hyz i
    apply Bool.le_iff_imp.mpr
    intro hi
    by_contra hn
    have yi : y i = false := Bool.eq_false_iff.mpr hn
    have ycut : y ≤ Function.update z i false := by
      intro j
      by_cases he : j = i
      · subst j; simp [yi]
      · simpa [Function.update_of_ne he] using hyz j
    have yes := Bool.le_iff_imp.mp (mono ycut) hy
    rw [hj i hi] at yes
    contradiction

theorem wire_clean_iff {n : ℕ} (I : Fin n → Fin n → Prop) (C : Circuit)
    (h : Monotone2 C) (w : ℕ) :
    Clean I (wire C w) ↔ ∀ z : Input n,
      wire C w z = true →
      (∀ i, z i = true → wire C w (Function.update z i false) = false) →
      points z = z ∨ lines z = z ∨ hits I z := by
  rw [clean_iff_minterms I _ (wire_monotone C h w)]
  simp only [minimal_iff_deletions _ (wire_monotone C h w), and_imp]

end IncidenceMinterms
