import CPRank
import Control

/-! Rounding depth of an unrestricted CP derivation for PHP(4,3).
Additions and multiplication preserve depth. Each division may raise it by one. -/
namespace PHPRoundingDepth
open PEqualNP.Search PHPThird.CP
open PEqualNP.Outside.L_meta_9682.Certificate (pigeon pair pigeonMem pairMem)

def level : ℕ → Set Line
  | 0 => {e | Unrounded e}
  | r+1 => {e | Linear {f | f ∈ level r ∨ ∃ (p : Line) (d : ℕ), p ∈ level r ∧ 0 < d ∧
        (∀ v, (d:ℤ) ∣ p.1 v) ∧ f = divide d p} e}

theorem carry {r e} (h : e ∈ level r) : e ∈ level (r+1) := Linear.start (Or.inl h)

theorem join {r e f} (h : e ∈ level r) (g : f ∈ level r) : plus e f ∈ level r := by
  cases r <;> exact Linear.add h g

theorem scale {r e} (k : ℕ) (h : e ∈ level r) : times k e ∈ level r := by
  cases r <;> exact Linear.mul k h

theorem cut {r e} (d : ℕ) (h : e ∈ level r) (hd : 0 < d)
    (dvd : ∀ v, (d:ℤ) ∣ e.1 v) : divide d e ∈ level (r+1) :=
  Linear.start (Or.inr ⟨e,d,h,hd,dvd,rfl⟩)

def edge (j : Fin 3) (a b : Fin 4) : Line := clauseCP (pair j a b)
def rowLine (a : Fin 4) : Line := clauseCP (pigeon a)

theorem edge_zero {j a b} (ne : a ≠ b) : edge j a b ∈ level 0 :=
  Linear.start (Axiom.clause (pairMem j a b ne))
theorem row_zero (a : Fin 4) : rowLine a ∈ level 0 := Linear.start (Axiom.clause (pigeonMem a))

def triangleSum (j : Fin 3) := plus (plus (edge j 0 1) (edge j 0 2)) (edge j 1 2)
def triangle (j : Fin 3) := divide 2 (triangleSum j)
def spokes (j : Fin 3) := plus (plus (edge j 0 3) (edge j 1 3)) (edge j 2 3)
def columnSum (j : Fin 3) := plus (times 2 (triangle j)) (spokes j)
def capacity (j : Fin 3) := divide 3 (columnSum j)

theorem triangle_one (j : Fin 3) : triangle j ∈ level 1 := by
  apply cut 2 (join (join (edge_zero (by decide)) (edge_zero (by decide))) (edge_zero (by decide))) (by decide)
  revert j
  decide +kernel

theorem capacity_two (j : Fin 3) : capacity j ∈ level 2 := by
  have star : spokes j ∈ level 0 :=
    join (join (edge_zero (by decide)) (edge_zero (by decide))) (edge_zero (by decide))
  apply cut 3 (join (scale 2 (triangle_one j)) (carry star)) (by decide)
  clear star
  revert j
  decide +kernel

def conclusion := plus (plus (plus (rowLine 0) (rowLine 1)) (plus (rowLine 2) (rowLine 3)))
  (plus (plus (capacity 0) (capacity 1)) (capacity 2))

theorem rankTwo : ((0 : V4 → ℤ), (1 : ℤ)) ∈ level 2 := by
  have rows := join (join (row_zero 0) (row_zero 1)) (join (row_zero 2) (row_zero 3))
  have cols := join (join (capacity_two 0) (capacity_two 1)) (capacity_two 2)
  have h : conclusion ∈ level 2 := join (carry (carry rows)) cols
  have ident : conclusion = ((0 : V4 → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) (by decide +kernel)
  exact ident ▸ h

theorem exactDepth : ((0 : V4 → ℤ), (1 : ℤ)) ∈ level 2 ∧
    ((0 : V4 → ℤ), (1 : ℤ)) ∉ level 1 ∧ ((0 : V4 → ℤ), (1 : ℤ)) ∉ level 0 :=
  ⟨rankTwo, noRankOneRefutation, fun h => noRankOneRefutation (carry h)⟩

end PHPRoundingDepth
#print axioms PHPRoundingDepth.exactDepth
