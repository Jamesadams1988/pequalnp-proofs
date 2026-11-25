import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A signed count for collision boxes of five pigeons in four holes. -/
namespace Row133.SignedBoxes

private def eqCount (a b : Nat) : Nat := if a = b then 1 else 0

/-- Number of unordered pairs of pigeons assigned the same hole. -/
def equalPairs (a b c d e : Nat) : Nat :=
  eqCount a b + eqCount a c + eqCount a d + eqCount a e +
  eqCount b c + eqCount b d + eqCount b e +
  eqCount c d + eqCount c e + eqCount d e

def weight (a b c d e : Nat) : Int :=
  match equalPairs a b c d e with
  | 1 => 4
  | 2 => -1
  | _ => 0

/-- Five base-four digits in little-endian order. -/
def rowWeight (r : Nat) : Int :=
  weight (r%4) ((r/4)%4) ((r/16)%4) ((r/64)%4) ((r/256)%4)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem total : ∑ r ∈ Finset.range 1024, rowWeight r = 600 := by decide +kernel

/-- The first two pigeons occupy hole 0. The other three factors are arbitrary
subsets of holes 1, 2 and 3, specified by three-bit masks. -/
def normalizedWeight (A B C : Fin 8) : Int :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ∑ c ∈ Finset.range 3,
    if A.val.testBit a && B.val.testBit b && C.val.testBit c then
      weight 0 0 (a+1) (b+1) (c+1) else 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem normalizedBound : ∀ A B C : Fin 8, normalizedWeight A B C ≤ 6 := by decide +kernel

/-- If any additional pigeon is also in the fixed hole, the three equal
pigeons already make at least three pairs, so all such rows contribute zero. -/
theorem zeroInNormalizedBox : ∀ a b c : Fin 4,
    (a=0 ∨ b=0 ∨ c=0) → weight 0 0 a.val b.val c.val = 0 := by decide +kernel

/-- A disjoint partition into pieces of signed weight at most six needs
at least a hundred pieces whenever the total signed weight is 600. -/
theorem partitionBound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (pieces : Finset β) (part : β → Finset α) (w : α → Int)
    (cover : pieces.biUnion part = rows)
    (sep : (↑pieces : Set β).PairwiseDisjoint part)
    (mass : ∑ a ∈ rows, w a = 600)
    (bound : ∀ b ∈ pieces, ∑ a ∈ part b, w a ≤ 6) : 100 ≤ pieces.card := by
  have h : (600 : Int) ≤ pieces.card * 6 := calc
    (600 : Int) = ∑ a ∈ pieces.biUnion part, w a := by rw [cover,mass]
    _ = ∑ b ∈ pieces, ∑ a ∈ part b, w a := Finset.sum_biUnion sep
    _ ≤ ∑ _b ∈ pieces, (6 : Int) := Finset.sum_le_sum bound
    _ = _ := by simp
  omega

end Row133.SignedBoxes
#print axioms Row133.SignedBoxes.total
#print axioms Row133.SignedBoxes.normalizedBound
#print axioms Row133.SignedBoxes.zeroInNormalizedBox
#print axioms Row133.SignedBoxes.partitionBound
