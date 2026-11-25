import Charging
import Restriction
import PGHexSequence

namespace Row4201
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PG4Separation Charging
open PGHexSequence (pref pair embedInput cycleAccepts)

/-- Any OR lower bound for the embedded six-cycle adds to 36 disjoint
gates in the projective-plane circuit. The local hypothesis permits all 42
input wires, including the 36 fixed to false on the tested core. -/
theorem liftCycle {b : ℕ}
    (coreBound : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 6 → Bool, D.eval (List.ofFn (embedInput x)) = cycleAccepts x) →
      b ≤ D.gates.countP isOr)
    (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔ PGSequence.accepts x) :
    36 + b ≤ C.gates.countP isOr := by
  classical
  let ready (j : Fin C.gates.length) : Prop := isOr C.gates[j] = true ∧
    ∀ w ∈ C.gates[j].inputs, prefixRead C j (pref 0) w = true
  let occupied := Finset.univ.filter ready
  have charges := lowerWithCore C hm 36 pref pair occupied
    (fun j hj => (Finset.mem_filter.mp hj).2) PGHexSequence.prefixMono
    (PGHexSequence.samples C computes) PGHexSequence.pairNext
  have smaller := Restrict.count_toCore_le C hm (pref 0) ready (fun _ a b => ⟨a,b⟩)
  have hc := coreBound (Restrict.toCore C (pref 0)) (Restrict.toCore_mono C hm _) (by
    intro x
    rw [Restrict.eval_toCore _ hm]
    have same : Restrict.mask (pref 0) (embedInput x) = embedInput x := by
      funext v
      unfold Restrict.mask
      cases h : embedInput x v with
      | false => simp
      | true => simp [PGHexSequence.embedBelowCore x v h]
    rw [same]
    exact PGHexSequence.computesCore C computes x)
  exact (Nat.add_le_add_left (hc.trans smaller) 36).trans charges

end Row4201
#print axioms Row4201.liftCycle
