import Unfold
import Emit

/-! Fan-in-two depth gives a size bound independent of the number of dead gates
in the supplied circuit. Research credit: James Adams. -/
namespace DepthSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem size_of_depth {n d : ℕ} (C : Circuit) (hC : FanInTwo C) (hd : C.depth n ≤ d) :
    HasCircuitSize n (circuitFun n C) (2 ^ d - 1) := by
  obtain ⟨t, hg, hc, he⟩ := exists_tree C n hC
  obtain ⟨D, hD, hs, hv⟩ := t.realize hg
  have hpow : 2 ^ C.depth n ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  exact ⟨D, hD, by omega, fun x => (hv x).trans (congrFun he x)⟩

theorem size_of_depth_four {n : ℕ} (C : Circuit) (hC : FanInTwo C) (hd : C.depth n ≤ 4) :
    HasCircuitSize n (circuitFun n C) 15 :=
  size_of_depth C hC hd

#print axioms size_of_depth
end DepthSize
