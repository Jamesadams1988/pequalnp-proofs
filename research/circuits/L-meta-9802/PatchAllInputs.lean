import PatchLower
import PEqualNP.Outside.L_meta_4795

/-! Black-box recovery can use all raw inputs; it still needs twelve gates. -/
namespace Row9802.Transfer.Patch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Row4201.PGSequence (accepts)
open PEqualNP.Outside.L_meta_4795_aux (relabel_size)

/-- Slot zero carries the punctured output, followed by all 42 raw input bits. -/
def visibleAll (x : Fin 42 → Bool) : Fin 43 → Bool := Fin.cases (visible x 0) x

/-- Identify raw boundary wires with their dedicated test bits. All remaining
raw wires follow bit zero along this restricted family of test assignments. -/
private def rawLabel : Fin 42 → Fin 13 :=
  ![1,8,9,0,0,10,0,0,0,0,0,0,0,0,0,11,0,12,0,0,0,3,2,0,0,0,4,0,5,0,0,0,0,0,0,0,0,0,6,0,0,7]

private def label : Fin 43 → Fin 13 := Fin.cases 0 rawLabel
private def lo (k j : Fin 13) : Bool :=
  if k=0 then false else decide (j = if k=1 then 3 else if k=2 then 8 else if k.val≤7 then 1 else 2)
private def hi (k : Fin 13) := Function.update (lo k) k (!(lo k k))

private theorem realizable : ∀ k : Fin 13,
    (∀ j, visibleAll (lo k ∘ rawLabel) j = (lo k ∘ label) j) ∧
    (∀ j, visibleAll (hi k ∘ rawLabel) j = (hi k ∘ label) j) := by decide +kernel

private theorem flips : ∀ k : Fin 13, ¬ accepts (lo k ∘ rawLabel) ∧ accepts (hi k ∘ rawLabel) := by
  decide +kernel

/-- This allows arbitrary raw primary inputs and the previous circuit's output.
Its internal gate outputs are not among the patch's inputs. Correctness is
required only when the old output agrees with the raw inputs. -/
theorem allInputsLower (D : Circuit) (legal : FanInTwo D)
    (computes : ∀ x, D.eval (List.ofFn (visibleAll x)) = true ↔ accepts x) :
    12 ≤ D.size := by
  let g := fun y : Fin 43 → Bool => D.eval (List.ofFn y)
  have hD : HasCircuitSize 43 g D.size := ⟨D,legal,le_rfl,fun _ => rfl⟩
  have hsmall := relabel_size label g D.size hD
  have dep (k : Fin 13) : ∃ y : Fin 13 → Bool,
      g (Function.update y k (!(y k)) ∘ label) ≠ g (y ∘ label) := by
    refine ⟨lo k,?_⟩
    change g (hi k ∘ label) ≠ g (lo k ∘ label)
    rw [←funext (realizable k).1,←funext (realizable k).2]
    intro equal
    have high := (computes _).mpr (flips k).2
    change g (visibleAll (hi k ∘ rawLabel)) = true at high
    exact (flips k).1 ((computes _).mp (equal.symm.trans high))
  have bound := Helpers.dep_lower 13 (fun y => g (y ∘ label)) dep D.size hsmall
  omega
end Row9802.Transfer.Patch
#print axioms Row9802.Transfer.Patch.allInputsLower
