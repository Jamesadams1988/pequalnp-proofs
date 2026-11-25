import Mathlib

/-! Exact certificates for the role of the twelve first-round triangle
inequalities in the four-pigeon, three-hole LP. -/

namespace PHPTriangleGeometry

abbrev P := Fin 4
abbrev H := Fin 3

/-- The triangle in column h omitting pigeon p. -/
def tri {R : Type} [AddCommMonoid R] (x : P → H → R) (p : P) (h : H) : R :=
  ∑ i : P, if i = p then 0 else x i h

/-- Doubled thirds, in units of one sixth. The distinguished column has
a violating triangle; its balanced perturbation is canceled in the next column. -/
def omittedWitness (p : P) (q : H) (i : P) (h : H) : ℤ :=
  if h = q then (if i = p then 0 else 3) else
  if h = q+1 then (if i = p then 4 else 1) else 2

/-- Every one of the twelve triangles is indispensable if the only
additional inequalities available are the base LP axioms and the other eleven triangles. -/
theorem primitive_irredundant :
    ∀ p : P, ∀ q : H,
      (∀ i h, 0 ≤ omittedWitness p q i h ∧ omittedWitness p q i h ≤ 6) ∧
      (∀ i, ∑ h : H, omittedWitness p q i h = 6) ∧
      (∀ i k h, i ≠ k → omittedWitness p q i h + omittedWitness p q k h ≤ 6) ∧
      (∀ i h, (i,h) ≠ (p,q) → tri (omittedWitness p q) i h ≤ 6) ∧
      tri (omittedWitness p q) p q = 9 := by decide +kernel

/-- Nine upper inequalities suffice after aggregation. For column zero take
the sum of its four triangle inequalities, and keep the eight individual
triangles for the other two columns. -/
theorem compressed_isolates (x : P → H → ℝ)
    (rows : ∀ i, 1 ≤ ∑ h, x i h)
    (aggregate : 3*(∑ i, x i 0) ≤ 4)
    (rest : ∀ i h, h ≠ 0 → tri x i h ≤ 1) :
    ∀ i h, x i h = 1/3 := by
  have r0 := rows 0
  have r1 := rows 1
  have r2 := rows 2
  have r3 := rows 3
  have a01 := rest 0 1 (by decide)
  have a11 := rest 1 1 (by decide)
  have a21 := rest 2 1 (by decide)
  have a31 := rest 3 1 (by decide)
  have a02 := rest 0 2 (by decide)
  have a12 := rest 1 2 (by decide)
  have a22 := rest 2 2 (by decide)
  have a32 := rest 3 2 (by decide)
  norm_num [tri, Fin.sum_univ_succ] at aggregate r0 r1 r2 r3 a01 a11 a21 a31 a02 a12 a22 a32
  intro i h
  fin_cases i <;> fin_cases h <;> norm_num <;> linarith only [aggregate,r0,r1,r2,r3,a01,a11,a21,a31,a02,a12,a22,a32]

end PHPTriangleGeometry
#print axioms PHPTriangleGeometry.primitive_irredundant
#print axioms PHPTriangleGeometry.compressed_isolates
