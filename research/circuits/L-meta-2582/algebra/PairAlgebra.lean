import PEqualNP.Defs

namespace FixedPairAlgebra

inductive Formula where
  | x | y | outside
  | join (a b : Formula)
  | meet (a b : Formula)
deriving DecidableEq

def counts : Formula → List (ℕ × ℕ)
  | .x => [(1, 0)]
  | .y => [(0, 1)]
  | .outside => []
  | .join a b => counts a ++ counts b
  | .meet a b => (counts a).flatMap fun u =>
      (counts b).map fun v => (u.1 + v.1, u.2 + v.2)

def fits (e : Formula) (i j : ℕ) : Bool :=
  (counts e).any fun u => decide (u.1 ≤ i ∧ u.2 ≤ j)

theorem fits_iff (e : Formula) (i j : ℕ) :
    fits e i j = true ↔ ∃ u ∈ counts e, u.1 ≤ i ∧ u.2 ≤ j := by
  simp [fits]

theorem join_fits (a b : Formula) (i j : ℕ) :
    fits (.join a b) i j = (fits a i j || fits b i j) := by
  simp [fits, counts]

theorem meet_fits (a b : Formula) (i j : ℕ) :
    fits (.meet a b) i j = true ↔
    ∃ k ≤ i, ∃ l ≤ j, fits a k l = true ∧ fits b (i-k) (j-l) = true := by
  simp only [fits_iff, counts, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, hi, hj⟩
    exact ⟨u.1, by omega, u.2, by omega, ⟨u, hu, le_rfl, le_rfl⟩, v, hv,
      by omega, by omega⟩
  · rintro ⟨k, hk, l, hl, ⟨u, hu, hux, huy⟩, v, hv, hvx, hvy⟩
    exact ⟨_, ⟨u, hu, v, hv, rfl⟩, by omega, by omega⟩

theorem counts_positive (e : Formula) : ∀ u ∈ counts e, 0 < u.1 + u.2 := by
  induction e with
  | x => simp [counts]
  | y => simp [counts]
  | outside => simp [counts]
  | join a b ha hb =>
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact ha u h
    · exact hb u h
  | meet a b ha hb =>
    intro u hu
    obtain ⟨r, hr, s, hs, rfl⟩ := (by simpa only [counts, List.mem_flatMap, List.mem_map] using hu)
    have := ha r hr
    omega

theorem zero_impossible (e : Formula) : fits e 0 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨r, hr, hx, hy⟩ := (fits_iff ..).mp h
  have := counts_positive e r hr
  omega

theorem fits_mono (e : Formula) {i j k l : ℕ} (hi : i ≤ k) (hj : j ≤ l) :
    fits e i j = true → fits e k l = true := by
  simp only [fits_iff]
  rintro ⟨u, hu, hx, hy⟩
  exact ⟨u, hu, hx.trans hi, hy.trans hj⟩

abbrev Thresholds := Fin 4 × Fin 4 × Fin 4

def good (p : Thresholds) : Prop :=
  0 < p.1 ∧ p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.2.1

instance (p : Thresholds) : Decidable (good p) := by unfold good; infer_instance

theorem profile_count : (Finset.univ.filter good).card = 19 := by decide

def first (a b c : Bool) : Fin 4 := if a then 0 else if b then 1 else if c then 2 else 3

theorem first_anti : ∀ a b c d e f : Bool,
    (a = true → d = true) → (b = true → e = true) → (c = true → f = true) →
    first d e f ≤ first a b c := by decide

theorem first_pos : ∀ b c : Bool, 0 < first false b c := by decide

theorem first_spec : ∀ a b c : Bool, (a = true → b = true) → (b = true → c = true) →
    ∀ j : Fin 3, decide ((first a b c).val ≤ j.val) = ![a,b,c] j := by decide

def row (e : Formula) (i : ℕ) : Fin 4 := first (fits e i 0) (fits e i 1) (fits e i 2)

def profile (e : Formula) : Thresholds := (row e 0, row e 1, row e 2)

theorem row_anti (e : Formula) {i k : ℕ} (h : i ≤ k) : row e k ≤ row e i :=
  first_anti _ _ _ _ _ _ (fits_mono e h le_rfl) (fits_mono e h le_rfl)
    (fits_mono e h le_rfl)

theorem profile_good (e : Formula) : good (profile e) := by
  refine ⟨?_, row_anti e (by decide : 0 ≤ 1), row_anti e (by decide : 1 ≤ 2)⟩
  change 0 < first (fits e 0 0) _ _
  rw [zero_impossible]
  exact first_pos _ _

def read (p : Thresholds) (i j : Fin 3) : Bool :=
  decide ((![p.1,p.2.1,p.2.2] i).val ≤ j.val)

theorem row_spec (e : Formula) (i : ℕ) (j : Fin 3) :
    decide ((row e i).val ≤ j.val) = fits e i j.val := by
  have h := first_spec (fits e i 0) (fits e i 1) (fits e i 2)
    (fits_mono e le_rfl (by decide)) (fits_mono e le_rfl (by decide))
  fin_cases j
  · exact h 0
  · exact h 1
  · exact h 2

theorem read_profile (e : Formula) (i j : Fin 3) :
    read (profile e) i j = fits e i.val j.val := by
  fin_cases i <;> exact row_spec e _ j

inductive Context where
  | hole | appendX (c : Context) | appendY (c : Context)

def plug (e : Formula) : Context → Formula
  | .hole => e
  | .appendX c => .meet (plug e c) .x
  | .appendY c => .meet (plug e c) .y

structure Evaluator (Q : Type) where
  x : Q
  y : Q
  outside : Q
  join : Q → Q → Q
  meet : Q → Q → Q
  accept : Q → Bool

def run {Q : Type} (A : Evaluator Q) : Formula → Q
  | .x => A.x
  | .y => A.y
  | .outside => A.outside
  | .join a b => A.join (run A a) (run A b)
  | .meet a b => A.meet (run A a) (run A b)

theorem same_context {Q : Type} (A : Evaluator Q) {s t : Formula} (h : run A s = run A t)
    (c : Context) : run A (plug s c) = run A (plug t c) := by
  induction c with
  | hole => exact h
  | appendX c ih => exact congrArg (fun w => A.meet w A.x) ih
  | appendY c ih => exact congrArg (fun w => A.meet w A.y) ih

def witnesses : Fin 19 → Formula := ![
  (.join .y .x),
  (.join .y (.meet .x .x)),
  .y,
  (.join (.meet .y .y) .x),
  (.join (.join (.meet .y .y) (.meet .x .y)) (.meet .x .x)),
  (.join (.meet .y .y) (.meet .x .y)),
  (.join (.meet .y .y) (.meet .x .x)),
  (.join (.meet .y .y) (.meet (.meet .x .x) .y)),
  (.meet .y .y),
  .x,
  (.join (.meet .x .y) (.meet .x .x)),
  (.meet .x .y),
  (.join (.meet (.meet .x .y) .y) (.meet .x .x)),
  (.join (.meet (.meet .x .y) .y) (.meet (.meet .x .x) .y)),
  (.meet (.meet .x .y) .y),
  (.meet .x .x),
  (.meet (.meet .x .x) .y),
  (.meet (.meet (.meet .x .x) .y) .y),
  (.meet (.meet .x .x) .x)]

def tests : Fin 9 → Context := ![
  (.appendY (.appendY (.appendX (.appendX .hole)))),
  (.appendY (.appendX (.appendX .hole))),
  (.appendX (.appendX .hole)),
  (.appendY (.appendY (.appendX .hole))),
  (.appendY (.appendX .hole)),
  (.appendX .hole),
  (.appendY (.appendY .hole)),
  (.appendY .hole),
  .hole]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem tests_distinguish : ∀ i j : Fin 19, i ≠ j →
    ∃ k : Fin 9, fits (plug (witnesses i) (tests k)) 2 2 ≠
      fits (plug (witnesses j) (tests k)) 2 2 := by decide

theorem evaluator_injective {Q : Type} (A : Evaluator Q)
    (exactAtOutput : ∀ e, A.accept (run A e) = fits e 2 2) :
    Function.Injective (fun i : Fin 19 => run A (witnesses i)) := by
  intro i j h
  by_contra hn
  obtain ⟨k, hk⟩ := tests_distinguish i j hn
  apply hk
  rw [← exactAtOutput, ← exactAtOutput, same_context A h (tests k)]

theorem evaluator_card {Q : Type} [Fintype Q] (A : Evaluator Q)
    (exactAtOutput : ∀ e, A.accept (run A e) = fits e 2 2) : 19 ≤ Fintype.card Q := by
  simpa using Fintype.card_le_of_injective _ (evaluator_injective A exactAtOutput)



theorem fits_congr {a b : Formula} (h : profile a = profile b)
    {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2) : fits a i j = fits b i j := by
  let k : Fin 3 := ⟨i, by omega⟩
  let l : Fin 3 := ⟨j, by omega⟩
  exact (read_profile a k l).symm.trans ((congrArg (fun p => read p k l) h).trans
    (read_profile b k l))

theorem profile_ext {a b : Formula}
    (h : ∀ i ≤ 2, ∀ j ≤ 2, fits a i j = fits b i j) : profile a = profile b := by
  have hr (i : ℕ) (hi : i ≤ 2) : row a i = row b i := by
    simp only [row, h i hi 0 (by decide), h i hi 1 (by decide), h i hi 2 (by decide)]
  exact Prod.ext (hr 0 (by decide)) (Prod.ext (hr 1 (by decide)) (hr 2 (by decide)))

theorem join_congr {a b c d : Formula} (ha : profile a = profile c)
    (hb : profile b = profile d) : profile (.join a b) = profile (.join c d) := by
  apply profile_ext
  intro i hi j hj
  simp only [join_fits, fits_congr ha hi hj, fits_congr hb hi hj]

theorem meet_transfer {a b c d : Formula} (ha : profile a = profile c)
    (hb : profile b = profile d) {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2)
    (h : fits (.meet a b) i j = true) : fits (.meet c d) i j = true := by
  obtain ⟨k, hk, l, hl, hx, hy⟩ := (meet_fits ..).mp h
  apply (meet_fits ..).mpr
  refine ⟨k, hk, l, hl, ?_, ?_⟩
  · rwa [← fits_congr ha (hk.trans hi) (hl.trans hj)]
  · rwa [← fits_congr hb (by omega : i-k ≤ 2) (by omega : j-l ≤ 2)]

theorem meet_congr {a b c d : Formula} (ha : profile a = profile c)
    (hb : profile b = profile d) : profile (.meet a b) = profile (.meet c d) := by
  apply profile_ext
  intro i hi j hj
  apply Bool.eq_iff_iff.mpr
  exact ⟨meet_transfer ha hb hi hj, meet_transfer ha.symm hb.symm hi hj⟩

set_option maxHeartbeats 5000000 in
theorem all_reachable : ∀ p : Thresholds, good p → ∃ i : Fin 19, profile (witnesses i) = p := by
  decide

abbrev States := ↥(Finset.univ.filter good)
def encode (e : Formula) : States := ⟨profile e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, profile_good e⟩⟩

noncomputable def representative (p : States) : Formula :=
  witnesses (Classical.choose (all_reachable p.val (Finset.mem_filter.mp p.property).2))

theorem representative_spec (p : States) : profile (representative p) = p.val :=
  Classical.choose_spec (all_reachable p.val (Finset.mem_filter.mp p.property).2)

noncomputable def upper : Evaluator States where
  x := encode .x
  y := encode .y
  outside := encode .outside
  join p q := encode (.join (representative p) (representative q))
  meet p q := encode (.meet (representative p) (representative q))
  accept p := read p.val 2 2

theorem upper_run (e : Formula) : run upper e = encode e := by
  induction e with
  | x => rfl
  | y => rfl
  | outside => rfl
  | join a b ha hb =>
    simp only [run, ha, hb]
    apply Subtype.ext
    exact join_congr (representative_spec _) (representative_spec _)
  | meet a b ha hb =>
    simp only [run, ha, hb]
    apply Subtype.ext
    exact meet_congr (representative_spec _) (representative_spec _)

theorem upper_correct (e : Formula) : upper.accept (run upper e) = fits e 2 2 := by
  rw [upper_run]
  exact read_profile e 2 2

theorem exact_state_count :
    (∃ (Q : Type) (I : Fintype Q) (A : Evaluator Q), @Fintype.card Q I = 19 ∧
      ∀ e, A.accept (run A e) = fits e 2 2) ∧
    (∀ (Q : Type) [Fintype Q] (A : Evaluator Q),
      (∀ e, A.accept (run A e) = fits e 2 2) → 19 ≤ Fintype.card Q) := by
  refine ⟨⟨States, inferInstance, upper, ?_, upper_correct⟩, fun _ _ => evaluator_card⟩
  simpa using profile_count

#print axioms exact_state_count
end FixedPairAlgebra
