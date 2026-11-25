import PEqualNP.Defs

/-! On a perfect matching there are circuits with dirty ANDs whose only mixed
independent witness uses an arbitrarily large number of active inputs. -/
namespace WideDefect

/-- The final wire of the chain is the last line input. Each preceding step
ANDs its line with the disjunction of its point and the rest of the chain. -/
def tail : (m : ℕ) → (Fin (m + 1) → Bool) → (Fin (m + 1) → Bool) → Bool
  | 0, _, L => L 0
  | m + 1, P, L => L 0 && (P 0 || tail m (fun i => P i.succ) (fun i => L i.succ))

def diagonal {m : ℕ} (P L : Fin (m + 1) → Bool) : Bool :=
  (List.ofFn (fun i => P i && L i)).any id

def dirty {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) : Bool :=
  a && (b || tail m P L)

def output {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) : Bool :=
  (dirty a b P L && b) || diagonal P L

theorem output_exact {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) :
    output a b P L = ((a && b) || diagonal P L) := by
  cases a <;> cases b <;> simp [output,dirty]

theorem tail_on_independent (m : ℕ) (P L : Fin (m + 1) → Bool)
    (h : ∀ i, L i = true → P i = false) :
    tail m P L = true ↔ ∀ i, L i = true := by
  induction m with
  | zero =>
    simp only [tail]
    constructor
    · intro t i
      have eq : i = 0 := Fin.ext (by have := i.isLt; omega)
      simpa only [eq] using t
    · exact fun t => t 0
  | succ m ih =>
    simp only [tail,Bool.and_eq_true,Bool.or_eq_true]
    constructor
    · rintro ⟨h0,hrest⟩
      have rest : tail m (fun i => P i.succ) (fun i => L i.succ) = true := by
        rcases hrest with hp | hr
        · simp [h 0 h0] at hp
        · exact hr
      exact Fin.cases h0 ((ih _ _ (fun i => h i.succ)).mp rest)
    · intro hall
      exact ⟨hall 0,Or.inr ((ih _ _ (fun i => h i.succ)).mpr (fun i => hall i.succ))⟩

theorem no_diagonal_iff {m : ℕ} (P L : Fin (m + 1) → Bool) :
    diagonal P L = false ↔ ∀ i, L i = true → P i = false := by
  have positive : diagonal P L = true ↔ ∃ i, P i = true ∧ L i = true := by
    simp [diagonal, List.any_eq_true]
    constructor
    · rintro (h | ⟨i,h⟩)
      · exact ⟨0,h⟩
      · exact ⟨i.succ,h⟩
    · rintro ⟨i,h⟩
      cases i using Fin.cases with
      | zero => exact Or.inl h
      | succ j => exact Or.inr ⟨j,h⟩
  constructor
  · intro h i hl
    apply Bool.eq_false_iff.mpr
    intro hp
    have hit := positive.mpr ⟨i, hp, hl⟩
    simp [h] at hit
  · intro h
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨i,hp,hl⟩ := positive.mp hit
    simp [h i hl] at hp

/-- Of all independent inputs, exactly one activates the distinguished AND:
the first point and every line other than its partner, with no other input on. -/
theorem unique_obstruction {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) :
    output a b P L = false ∧ dirty a b P L = true ↔
    a = true ∧ b = false ∧ (∀ i, P i = false) ∧ (∀ i, L i = true) := by
  rw [output_exact]
  constructor
  · rintro ⟨hneg,hd⟩
    obtain ⟨ha,hv⟩ := Bool.and_eq_true_iff.mp hd
    have hb : b = false := by cases b <;> simp_all
    have hdiag : diagonal P L = false := by simpa [ha,hb] using hneg
    have hind := (no_diagonal_iff P L).mp hdiag
    have htail : tail m P L = true := by simpa [hb] using hv
    have allL := (tail_on_independent m P L hind).mp htail
    exact ⟨ha,hb,fun i => hind i (allL i),allL⟩
  · rintro ⟨rfl,rfl,hp,hl⟩
    have hind : ∀ i, L i = true → P i = false := fun i _ => hp i
    simp [dirty, (no_diagonal_iff _ _).mpr hind, (tail_on_independent m P L hind).mpr hl]

/-- On both one-sided projections the distinguished AND is always false. -/
theorem pure_projections {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) :
    dirty a false P (fun _ => false) = false ∧ dirty false b (fun _ => false) L = false := by
  have h : tail m P (fun _ => false) = false := by cases m <;> rfl
  simp [dirty,h]

/-- Every AND that finishes a suffix of the chain is clean: on an independent
input, clearing all points preserves the value of that suffix. -/
theorem tail_line_projection (m : ℕ) (P L : Fin (m + 1) → Bool)
    (h : diagonal P L = false) : tail m P L = tail m (fun _ => false) L := by
  apply Bool.eq_iff_iff.mpr
  rw [tail_on_independent m P L ((no_diagonal_iff _ _).mp h),
    tail_on_independent m (fun _ => false) L (by simp)]

/-- Count the two distinguished inputs and the two sets of remaining inputs. -/
def weight {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool) : ℕ :=
  a.toNat + b.toNat + (Finset.univ.filter (fun i => P i = true)).card +
    (Finset.univ.filter (fun i => L i = true)).card

theorem defect_weight {m : ℕ} (a b : Bool) (P L : Fin (m + 1) → Bool)
    (independent : output a b P L = false) (active : dirty a b P L = true) :
    weight a b P L = m + 2 := by
  obtain ⟨rfl,rfl,hp,hl⟩ := (unique_obstruction a b P L).mp ⟨independent,active⟩
  simp [weight,hp,hl]
  omega

theorem defect_exists (m : ℕ) :
    let P : Fin (m+1) → Bool := fun _ => false
    let L : Fin (m+1) → Bool := fun _ => true
    output true false P L = false ∧ dirty true false P L = true := by
  apply (unique_obstruction ..).mpr
  simp

end WideDefect
