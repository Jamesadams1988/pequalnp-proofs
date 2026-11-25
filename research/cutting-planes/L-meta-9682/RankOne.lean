import PEqualNP.Defs

/-! A single Chvátal–Gomory closure of the pairwise clique relaxation still
contains the point with every coordinate 1/3. Upper inequalities a·x ≤ b
are used here so rounding is the ordinary integer floor on the right. -/
namespace CliqueCut

structure Upper (n : ℕ) where
  coeff : Fin n → ℤ
  rhs : ℤ

def Upper.holds {n} (e : Upper n) (den : ℤ) (x : Fin n → ℤ) : Prop :=
  ∑ i, e.coeff i * x i ≤ den * e.rhs

def add {n} (e f : Upper n) : Upper n := ⟨fun i => e.coeff i + f.coeff i, e.rhs+f.rhs⟩
def scale {n} (k : ℕ) (e : Upper n) : Upper n := ⟨fun i => (k:ℤ)*e.coeff i, (k:ℤ)*e.rhs⟩
def unit {n} (j : Fin n) (i : Fin n) : ℤ := if i = j then 1 else 0

/-- Unrounded consequences of the pair and Boolean axioms of one clique. -/
inductive Raw (n : ℕ) : Upper n → Prop
  | lo (i : Fin n) : Raw n ⟨fun j => -unit i j, 0⟩
  | hi (i : Fin n) : Raw n ⟨unit i, 1⟩
  | pair (i j : Fin n) (ne : i ≠ j) : Raw n ⟨fun k => unit i k + unit j k, 1⟩
  | plus {e f} : Raw n e → Raw n f → Raw n (add e f)
  | times (k : ℕ) {e} : Raw n e → Raw n (scale k e)

/-- Divisibility is expressed by writing every parent coefficient as d*a_i. -/
inductive RankOne (n : ℕ) : Upper n → Prop
  | raw {e} : Raw n e → RankOne n e
  | cut (a : Fin n → ℤ) (b d : ℤ) (hd : 0 < d) :
      Raw n ⟨fun i => d*a i,b⟩ → RankOne n ⟨a,b/d⟩
  | plus {e f} : RankOne n e → RankOne n f → RankOne n (add e f)
  | times (k : ℕ) {e} : RankOne n e → RankOne n (scale k e)

theorem addHolds {n d x} {e f : Upper n} (he : e.holds d x) (hf : f.holds d x) :
    (add e f).holds d x := by
  simp only [Upper.holds, add, add_mul, Finset.sum_add_distrib, mul_add] at *
  omega

theorem scaleHolds {n d x} (k : ℕ) {e : Upper n} (h : e.holds d x) :
    (scale k e).holds d x := by
  change (∑ i, ((k:ℤ)*e.coeff i)*x i) ≤ d*((k:ℤ)*e.rhs)
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [mul_left_comm d (k:ℤ)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem dotUnit {n} (x : Fin n → ℤ) (i : Fin n) :
    (∑ j, unit i j * x j) = x i := by simp [unit, ite_mul]

theorem rawHolds {n} {e : Upper n} (h : Raw n e) {d : ℤ} {x : Fin n → ℤ}
    (lo : ∀ i, 0 ≤ x i) (hi : ∀ i, x i ≤ d) (pair : ∀ i j, i ≠ j → x i+x j ≤ d) :
    e.holds d x := by
  induction h with
  | lo i => simp [Upper.holds, neg_mul, dotUnit, lo]
  | hi i => simpa [Upper.holds, dotUnit] using hi i
  | pair i j ne => simpa [Upper.holds, add_mul, Finset.sum_add_distrib, dotUnit] using pair i j ne
  | plus _ _ he hf => exact addHolds he hf
  | times k _ he => exact scaleHolds k he

/-- Arithmetic form of the one-round bound, valid in every dimension. -/
theorem roundThird {ι : Type} [Fintype ι] (a : ι → ℤ) {b d : ℤ} (hd : 0 < d) (hb : 0 ≤ b)
    (singles : ∀ i, d*a i ≤ b) (half : d*(∑ i, max (a i) 0) ≤ 2*b) :
    (∑ i, a i) ≤ 3*(b/d) := by
  let q := b/d
  change (∑ i, a i) ≤ 3*q
  have hq : 0 ≤ q := Int.ediv_nonneg hb hd.le
  have upper : b < (q+1)*d := (Int.ediv_lt_iff_lt_mul hd).mp (by change q < q+1; omega)
  by_cases one : 1 ≤ q
  · have lt : (∑ i, max (a i) 0) < 2*(q+1) := by
      apply (Int.mul_lt_mul_left hd).mp
      nlinarith
    have le : (∑ i, a i) ≤ ∑ i, max (a i) 0 := Finset.sum_le_sum fun i _ => le_max_left _ _
    omega
  · have eq : q = 0 := by omega
    have cut : b < d := by simpa [eq] using upper
    have neg (i : ι) : a i ≤ 0 := by
      by_contra! pos
      have hle := mul_le_mul_of_nonneg_left (show 1 ≤ a i by omega) hd.le
      have hs := singles i
      linarith
    simpa [eq] using (Finset.sum_nonpos fun i (_ : i ∈ (Finset.univ : Finset ι)) => neg i)

private theorem rawRoundThird {n} (a : Fin n → ℤ) (b d : ℤ) (hd : 0 < d)
    (raw : Raw n ⟨fun i => d*a i,b⟩) : (∑ i, a i) ≤ 3*(b/d) := by
  have zero := rawHolds raw (d := 1) (x := fun _ => 0) (by simp) (by simp) (by simp)
  have hz : 0 ≤ b := by simpa [Upper.holds] using zero
  apply roundThird a hd hz
  · intro j
    have hs := rawHolds raw (d := 1) (x := unit j)
      (by intro i; simp [unit]; split <;> omega)
      (by intro i; simp [unit]; split <;> omega)
      (by intro i k ne; by_cases h : i = j <;> by_cases h' : k = j <;> simp_all [unit])
    simpa [Upper.holds, unit, mul_ite] using hs
  · let x (i : Fin n) : ℤ := if 0 ≤ a i then 1 else 0
    have lo (i) : 0 ≤ x i := by simp [x]; split <;> omega
    have hi (i) : x i ≤ 1 := by simp [x]; split <;> omega
    have hs := rawHolds raw (d := 2) (x := x) lo (fun i => by have := hi i; omega)
      (fun i j _ => by have := hi i; have := hi j; omega)
    change (∑ i, (d*a i)*x i) ≤ 2*b at hs
    rw [Finset.mul_sum]
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [x, hi]
    · simp [x, hi, max_eq_right (by omega : a i ≤ 0)]

theorem uniformThird {n} {e : Upper n} (h : RankOne n e) : e.holds 3 (fun _ => 1) := by
  induction h with
  | raw he => exact rawHolds he (by simp) (by simp) (by simp)
  | cut a b d hd hr => simpa [Upper.holds] using rawRoundThird a b d hd hr
  | plus _ _ he hf => exact addHolds he hf
  | times k _ he => exact scaleHolds k he

theorem cliqueFourNeedsTwoRounds : ¬ RankOne 4 ⟨fun _ => 1,1⟩ := by
  intro h
  have := uniformThird h
  change (∑ _ : Fin 4, (1 : ℤ)*1) ≤ 3*1 at this
  exact (by decide +kernel : ¬ (∑ _ : Fin 4, (1 : ℤ)*1) ≤ 3*1) this

end CliqueCut
#print axioms CliqueCut.roundThird
#print axioms CliqueCut.cliqueFourNeedsTwoRounds
