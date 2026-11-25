import CodeToHex
import DagToCode
import PGHexSequence

/-! Application of straight-OR normalization to an induced six-cycle. The
only finite search premise is explicit, so the circuit-to-program reduction
can also be used with a separately verified SAT certificate. -/
namespace HexNormalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Row4201.HexFour Row4201.PGHexSequence

def asRow (x : BitVec 6) (i : Fin 6) := x.getLsbD i.val

private def mask (v : Fin 42) : BitVec 6 :=
  if v=0 then 1 else if v=1 then 2 else if v=2 then 4 else if v=28 then 8 else
  if v=21 then 16 else if v=22 then 32 else 63

private theorem embeddedBit : ∀ v : Fin 42, ∀ x : BitVec 6, x ≠ 63 →
    meet x (mask v) = embedInput (asRow x) v := by decide +kernel

private theorem readFn {n} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if hi : i < n then f ⟨i,hi⟩ else false := by
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,
      List.length_ofFn,h,dite_true,List.getElem_ofFn,Option.getD_some]
  · simp [List.getD_eq_getElem?_getD,h]

private theorem physicalRep : Rep Code.start (fun x => List.ofFn (embedInput (asRow x))) := by
  intro i
  by_cases hi : i < 42
  · exact ⟨mask ⟨i,hi⟩,fun x hx => by simpa only [readFn,dite_eq_left hi,wires] using embeddedBit ⟨i,hi⟩ x hx⟩
  · simpa only [readFn,dite_eq_right hi] using bot (by decide) Code.start

theorem smallProgram (C : Circuit) (hm : Monotone2 C)
    (small : C.gates.countP ZeroSensitivity.isOr ≤ 4) (w : BitVec 6 → List Bool)
    (len : ∀ x, (w x).length = (w 0).length) (hr : Rep Code.start w) :
    ∃ p : Program, ∀ x, x ≠ 63 → run p x = C.eval (w x) := by
  obtain ⟨k,c,hk,_,hc⟩ := circuitToCode C hm small w len hr
  have h : k+(4-k)=4 := by omega
  obtain ⟨z,hz⟩ := pad c (4-k) (by omega)
  have ep : Has z (fun x => C.eval (w x)) := hz _ hc
  have good : ∃ q : Code (k+(4-k)), Has q (fun x => C.eval (w x)) := ⟨z,ep⟩
  rw [h] at good
  obtain ⟨q,hq⟩ := good
  exact programOfCode q hq

theorem embeddedFive (reject : ∀ p : Program, ¬ agrees p)
    (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn (embedInput x)) = cycleAccepts x) :
    5 ≤ C.gates.countP ZeroSensitivity.isOr := by
  by_contra! small
  obtain ⟨p,hp⟩ := smallProgram C hm (by omega) _ (fun _ => by simp) physicalRep
  have eq (x : BitVec 6) (hx : x ≠ 63) : run p x = cycleAccepts (asRow x) :=
    (hp x hx).trans (hc _)
  apply reject p
  unfold agrees
  repeat' apply And.intro
  all_goals (rw [eq _ (by decide)]; decide)

end HexNormalize
#print axioms HexNormalize.embeddedFive
