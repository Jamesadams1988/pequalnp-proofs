import Lower39

namespace Row9802.Connected
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Row4201.Charging
open Row9802.SixCycle (tests literal)

def rank : Fin 40 → ℕ := ![0,6,7,2,15,8,11,16,19,21,23,25,27,3,30,4,12,9,13,17,1,5,10,14,18,20,22,24,26,28,29,31,32,33,34,35,36,37,38,39]
def parents : Fin 38 → Fin 40 := ![20,20,20,15,21,21,21,21,2,22,22,22,3,23,23,23,4,24,0,25,1,26,0,27,1,28,2,3,30,4,5,6,7,8,9,0,1,2]
def prefSet (k : ℕ) (v : Fin 40) : Bool := decide (rank v < k+2)
def pair (k : Fin 38) (v : Fin 40) : Bool := decide (v=parents k ∨ rank v=k.val+2)

set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem samples : ∀ k : Fin 38, tests (prefSet k.val) = true ∧ tests (pair k)=true ∧
    tests (fun v => prefSet k.val v && pair k v) = false := by decide +kernel

theorem containsPair : ∀ k : Fin 38, ∀ v, pair k v = true → prefSet (k.val+1) v = true := by decide +kernel

theorem lower38 (C : Circuit) (hm : Monotone2 C) (correct : ∀ x, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 40, (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true) :
    38 ≤ C.gates.countP isOr := by
  have eq (x : Fin 40 → Bool) : C.eval (List.ofFn x) = tests x :=
    Bool.eq_iff_iff.mpr ((correct x).trans (literal x).symm)
  exact lower C hm 38 prefSet pair
    (by intro i j h v hv; simp only [prefSet,decide_eq_true_eq] at *; omega)
    (by intro k; simpa only [eq] using samples k) containsPair

end Row9802.Connected
#print axioms Row9802.Connected.lower38
