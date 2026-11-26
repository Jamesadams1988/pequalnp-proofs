import Adaptive
import Lower

namespace ProjectiveEdge.Instance
open Finset PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.Forest ProjectiveEdge.Adaptive Row9769.Elimination

def adj : Fin 42 → ℕ := ![2474236706816,550433193984,1100866387968,2201732775936,5421137920,10842275840,21684551680,43369103360,86738206720,173476413440,346952826880,693905653760,1387811307520,2775622615040,1153200816128,2306401632256,214758850560,429517701120,859035402240,1718070804480,3436141608960,81938,163878,327756,655512,1311024,524897,1049794,2437,4874,9748,19496,38992,77984,155968,311936,623872,1247744,398337,796674,1593348,1089545]
def graph : SimpleGraph (V 41) where
  Adj i j := (adj i).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable ((adj i).testBit j.val = true))
def members (m : ℕ) : Finset (V 41) := univ.filter fun i => m.testBit i.val

theorem edgeMatch : ∀ i j : Fin 42, graph.Adj i j ↔ (i,j) ∈ edges ∨ (j,i) ∈ edges := by decide +kernel

theorem literalBridge (k : ℕ) (h : Bound graph (members 4398046511103) k) (s : ℕ)
    (hc : HasCircuitSize 42 literal s) : k ≤ s := by
  have full : members 4398046511103 = univ := by decide +kernel
  have eq : F (induced graph (members 4398046511103)) ∅ = target := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [F_true]
    simp only [Finset.notMem_empty, false_and, exists_false, false_or]
    constructor
    · rintro ⟨i,j,⟨_,_,eq⟩,xi,xj⟩
      rcases (edgeMatch i j).mp eq with f|r
      · exact List.any_eq_true.mpr ⟨(i,j),f,Bool.and_eq_true_iff.mpr ⟨xi,xj⟩⟩
      · exact List.any_eq_true.mpr ⟨(j,i),r,Bool.and_eq_true_iff.mpr ⟨xj,xi⟩⟩
    · intro good
      obtain ⟨⟨i,j⟩,he,bo⟩ := List.any_eq_true.mp good
      obtain ⟨xi,xj⟩ := Bool.and_eq_true_iff.mp bo
      exact ⟨i,j,⟨full ▸ mem_univ i,full ▸ mem_univ j,(edgeMatch i j).mpr (Or.inl he)⟩,xi,xj⟩
  have lit : literal = target := by funext x; simp [literal,target,edges,List.any_cons,Bool.or_assoc]
  have bound := h ∅ (by simp) s (eq.symm ▸ (lit ▸ hc))
  simpa using bound
end ProjectiveEdge.Instance
