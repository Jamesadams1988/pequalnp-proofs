import CPRank

/-! The first cutting-plane closure of PHP(4,3) has exactly one rational point. -/
namespace PHPThird.Point
open PEqualNP.Search PEqualNP.ProofComplexity
open PHPThird.CP

def holdsQ (x : V4 → ℚ) (e : Line) : Prop := (e.2:ℚ) ≤ ∑ v, (e.1 v:ℚ)*x v

def tripleRows : Fin 4 → Fin 4 × Fin 4 × Fin 4 := ![(1,2,3),(0,2,3),(0,1,3),(0,1,2)]
def edge (i k : Fin 4) (j : Fin 3) : Line := clauseCP {((i,j),false), ((k,j),false)}
def parent (k : Fin 4) (j : Fin 3) : Line :=
  let (a,b,c) := tripleRows k
  plus (edge a b j) (plus (edge a c j) (edge b c j))

def dotRow (i : Fin 4) : Line :=
  (fun v => unit (i,0) v + unit (i,1) v + unit (i,2) v, 1)
def dotTriple (k : Fin 4) (j : Fin 3) : Line :=
  let (a,b,c) := tripleRows k
  (fun v => -(unit (a,j) v + unit (b,j) v + unit (c,j) v), -1)

private theorem different : ∀ k : Fin 4, (tripleRows k).1 ≠ (tripleRows k).2.1 ∧
    (tripleRows k).1 ≠ (tripleRows k).2.2 ∧ (tripleRows k).2.1 ≠ (tripleRows k).2.2 := by decide +kernel

private theorem edgeRaw (i k : Fin 4) (j : Fin 3) (ne : i ≠ k) : Unrounded (edge i k j) :=
  Linear.start (Axiom.clause (.inr ⟨i,k,j,ne,rfl⟩))

theorem tripleInClosure (k : Fin 4) (j : Fin 3) : FirstClosure (dotTriple k j) := by
  have even : ∀ k j v, (2:ℤ) ∣ (parent k j).1 v := by decide +kernel
  have eq : ∀ k j, dotTriple k j = divide 2 (parent k j) := by decide +kernel
  have hk := different k
  have raw : Unrounded (parent k j) := Linear.add (edgeRaw _ _ _ hk.1)
    (Linear.add (edgeRaw _ _ _ hk.2.1) (edgeRaw _ _ _ hk.2.2))
  exact Linear.start (.inr ⟨parent k j,2,raw,by decide,even k j,eq k j⟩)

theorem rowInClosure (i : Fin 4) : FirstClosure (dotRow i) := by
  have eq : ∀ i : Fin 4, clauseCP (Finset.univ.image (fun j : Fin 3 => ((i,j),true))) = dotRow i := by
    decide +kernel
  rw [← eq]
  exact Linear.start (.inl (Linear.start (Axiom.clause (.inl ⟨i,rfl⟩))))

private theorem dotUnit (x : V4 → ℚ) (p : V4) : (∑ v, (unit p v : ℚ)*x v) = x p := by
  simp [unit,ite_mul]

theorem rowBound {x : V4 → ℚ} (h : ∀ e, FirstClosure e → holdsQ x e) (i : Fin 4) :
    1 ≤ x (i,0)+x (i,1)+x (i,2) := by
  simpa [holdsQ,dotRow,add_mul,Finset.sum_add_distrib,dotUnit] using h _ (rowInClosure i)

theorem tripleBound {x : V4 → ℚ} (h : ∀ e, FirstClosure e → holdsQ x e) (k : Fin 4) (j : Fin 3) :
    x ((tripleRows k).1,j)+x ((tripleRows k).2.1,j)+x ((tripleRows k).2.2,j) ≤ 1 := by
  have b := h _ (tripleInClosure k j)
  simp [holdsQ,dotTriple,add_mul,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib,dotUnit] at b
  linarith only [b]

/-- The four pigeon row sums and twelve triangle cuts leave no freedom in the first closure. -/
theorem unique (x : V4 → ℚ) :
    (∀ e, FirstClosure e → holdsQ x e) ↔ ∀ v, x v = 1/3 := by
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
    · change x (0,0) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (0,1) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (0,2) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (1,0) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (1,1) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (1,2) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (2,0) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (2,1) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (2,2) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (3,0) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (3,1) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
    · change x (3,2) = 1/3
      linarith only [r0, r1, r2, r3, t00, t01, t02, t10, t11, t12, t20, t21, t22, t30, t31, t32]
  · intro values e he
    have p : 3*e.2 ≤ ∑ v, e.1 v := by simpa [third,holdsAt] using firstClosureSound he
    have q : 3*(e.2 : ℚ) ≤ ∑ v, (e.1 v : ℚ) := by exact_mod_cast p
    unfold holdsQ
    simp_rw [values]
    rw [← Finset.sum_mul]
    linarith only [q]

end PHPThird.Point
#print axioms PHPThird.Point.unique
