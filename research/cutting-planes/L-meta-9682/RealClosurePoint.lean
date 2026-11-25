import FirstClosurePoint

/-! Extension of the singleton closure theorem over any ordered field. -/
namespace PHPThird.OrderedPoint
open PHPThird.CP PHPThird.Point
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def satisfies (x : V4 → K) (e : Line) : Prop := (e.2 : K) ≤ ∑ v, (e.1 v : K)*x v

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem dotUnit (x : V4 → K) (p : V4) : (∑ v, (unit p v : K)*x v) = x p := by
  simp [unit,ite_mul]

omit [IsStrictOrderedRing K] in
private theorem rowBound {x : V4 → K} (h : ∀ e, FirstClosure e → satisfies x e) (i : Fin 4) :
    1 ≤ x (i,0)+x (i,1)+x (i,2) := by
  simpa [satisfies,dotRow,add_mul,Finset.sum_add_distrib,dotUnit] using h _ (rowInClosure i)

private theorem tripleBound {x : V4 → K} (h : ∀ e, FirstClosure e → satisfies x e) (k : Fin 4) (j : Fin 3) :
    x ((tripleRows k).1,j)+x ((tripleRows k).2.1,j)+x ((tripleRows k).2.2,j) ≤ 1 := by
  have b := h _ (tripleInClosure k j)
  simp [satisfies,dotTriple,add_mul,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib,dotUnit] at b
  linarith only [b]

/-- The four pigeon row sums and twelve triangle cuts leave no freedom in the first closure. -/
theorem singleton (x : V4 → K) :
    (∀ e, FirstClosure e → satisfies x e) ↔ ∀ v, x v = 1/3 := by
  constructor
  · intro h
    have r0 := rowBound h 0
    have r1 := rowBound h 1
    have r2 := rowBound h 2
    have r3 := rowBound h 3
    have t00 : x (1,0) + x (2,0) + x (3,0) ≤ 1 := tripleBound h 0 0
    have t01 : x (1,1) + x (2,1) + x (3,1) ≤ 1 := tripleBound h 0 1
    have t02 : x (1,2) + x (2,2) + x (3,2) ≤ 1 := tripleBound h 0 2
    have t10 : x (0,0) + x (2,0) + x (3,0) ≤ 1 := tripleBound h 1 0
    have t11 : x (0,1) + x (2,1) + x (3,1) ≤ 1 := tripleBound h 1 1
    have t12 : x (0,2) + x (2,2) + x (3,2) ≤ 1 := tripleBound h 1 2
    have t20 : x (0,0) + x (1,0) + x (3,0) ≤ 1 := tripleBound h 2 0
    have t21 : x (0,1) + x (1,1) + x (3,1) ≤ 1 := tripleBound h 2 1
    have t22 : x (0,2) + x (1,2) + x (3,2) ≤ 1 := tripleBound h 2 2
    have t30 : x (0,0) + x (1,0) + x (2,0) ≤ 1 := tripleBound h 3 0
    have t31 : x (0,1) + x (1,1) + x (2,1) ≤ 1 := tripleBound h 3 1
    have t32 : x (0,2) + x (1,2) + x (2,2) ≤ 1 := tripleBound h 3 2
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j
    all_goals first
      | change x (0,0) = 1/3
      | change x (0,1) = 1/3
      | change x (0,2) = 1/3
      | change x (1,0) = 1/3
      | change x (1,1) = 1/3
      | change x (1,2) = 1/3
      | change x (2,0) = 1/3
      | change x (2,1) = 1/3
      | change x (2,2) = 1/3
      | change x (3,0) = 1/3
      | change x (3,1) = 1/3
      | change x (3,2) = 1/3
    all_goals linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
  · intro values e he
    have p : 3*e.2 ≤ ∑ v, e.1 v := by simpa [third,holdsAt] using firstClosureSound he
    have q : 3*(e.2 : K) ≤ ∑ v, (e.1 v : K) := by exact_mod_cast p
    unfold satisfies
    simp_rw [values]
    rw [← Finset.sum_mul]
    linarith only [q]

theorem realSingleton (x : V4 → ℝ) :
    (∀ e, FirstClosure e → satisfies x e) ↔ ∀ v, x v = 1/3 := singleton x

end PHPThird.OrderedPoint
#print axioms PHPThird.OrderedPoint.realSingleton
