import HexNormalize

namespace HexNormalize
open Row4201.HexFour

def inputBits (x : BitVec 6) : List Bool := List.ofFn (fun i : Fin 6 => x.getLsbD i.val)

private theorem selector : ∀ i : Fin 6, ∀ x : BitVec 6,
    meet x (1 <<< i.val) = x.getLsbD i.val := by decide +kernel

theorem initialRep : Rep Code.start inputBits := by
  intro i
  by_cases hi : i < 6
  · refine ⟨1 <<< i, fun x _ => ?_⟩
    have h := selector ⟨i,hi⟩ x
    interval_cases i <;> exact h
  · have h := bot (k := 0) (by decide) Code.start
    simpa [inputBits,List.getD_eq_getElem?_getD, hi] using h

theorem programOfCode (c : Code 4) {f} (hf : Has c f) :
    ∃ p : Program, ∀ x : BitVec 6, x ≠ 63 → run p x = f x := by
  obtain ⟨out,hs⟩ := hf
  cases c with
  | push c3 g h =>
    cases c3 with
    | push c2 e f =>
      cases c2 with
      | push c1 c d =>
        cases c1 with
        | push c0 a b =>
          cases c0
          exact ⟨⟨a,b,c,d,e,f,g,h,out⟩,hs⟩

end HexNormalize
#print axioms HexNormalize.initialRep
#print axioms HexNormalize.programOfCode
