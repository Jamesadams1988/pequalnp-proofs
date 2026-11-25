import Upper114
import EmbeddedFive
import HexFour
import Charging
import Restriction

namespace Row9802.SixCycle
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Row4201.Charging
open PG4Separation Row4201.HexFour

/-- Labels of incident pairs are copied from the official graph. The list
is shared with the checked 114-gate construction. -/
def tests (x : Fin 40 → Bool) : Bool := Upper114.edges.any (fun e =>
  x (Fin.ofNat 40 e.1) && x (Fin.ofNat 40 e.2))

theorem literal (x : Fin 40 → Bool) : tests x = true ↔ ∃ u v : Fin 40,
    (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true := by
  have bounds : ∀ e ∈ Upper114.edges, e.1 < 40 ∧ e.2 < 40 := by
    have h : Upper114.edges.all (fun e => decide (e.1 < 40 ∧ e.2 < 40)) = true := by decide +kernel
    intro e he
    exact of_decide_eq_true (List.all_eq_true.mp h e he)
  simp only [tests,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨e,he,hu,hv⟩
    obtain ⟨hp,hl⟩ := bounds e he
    exact ⟨⟨e.1,hp⟩,⟨e.2,hl⟩,he,by simpa [Fin.ofNat,Nat.mod_eq_of_lt hp] using hu,
      by simpa [Fin.ofNat,Nat.mod_eq_of_lt hl] using hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨(u.val,v.val),he,by simpa using hu,by simpa using hv⟩

def core (x : Fin 6 → Bool) (v : Fin 40) : Bool :=
  if v=0 then x 0
    else if v=2 then x 1
    else if v=3 then x 2
    else if v=20 then x 3
    else if v=27 then x 4
    else if v=22 then x 5 else false

/-- Rank in a connected vertex order, starting with the six-cycle. -/
def rank : Fin 40 → ℕ := ![0,15,1,2,19,16,6,7,8,23,25,9,27,10,30,11,12,17,13,20,3,14,5,18,21,22,24,4,26,28,29,31,32,33,34,35,36,37,38,39]
def parents : Fin 34 → Fin 40 := ![22,27,27,27,20,20,22,22,2,21,21,21,3,23,23,4,0,25,1,26,1,28,2,3,30,4,5,6,7,8,9,0,1,2]

def pref (k : ℕ) (v : Fin 40) : Bool := decide (rank v < k+6)
def pair (k : Fin 34) (v : Fin 40) : Bool := decide (v = parents k ∨ rank v = k.val+6)

set_option maxHeartbeats 0
set_option maxRecDepth 14000

theorem marks : ∀ (x : Fin 6 → Bool) v, core x v = true → pref 0 v = true := by decide +kernel
theorem coreValue : ∀ x, tests (core x) = Row4201.PGHexSequence.cycleAccepts x := by decide +kernel
theorem samples : ∀ k : Fin 34, tests (pref k.val) = true ∧ tests (pair k) = true ∧
    tests (fun v => pref k.val v && pair k v) = false := by decide +kernel
theorem witnessNext : ∀ k : Fin 34, ∀ v, pair k v = true → pref (k.val+1) v = true := by decide +kernel

private def mask (v : Fin 40) : BitVec 6 :=
  if v=0 then 1
    else if v=2 then 2
    else if v=3 then 4
    else if v=20 then 8
    else if v=27 then 16
    else if v=22 then 32 else 63

private theorem embeddedBit : ∀ v : Fin 40, ∀ x : BitVec 6, x ≠ 63 →
    meet x (mask v) = core (HexNormalize.asRow x) v := by decide +kernel

open HexNormalize
private theorem readFn {n} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if hi : i < n then f ⟨i,hi⟩ else false := by
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,
      List.length_ofFn,h,dite_true,List.getElem_ofFn,Option.getD_some]
  · simp [List.getD_eq_getElem?_getD,h]

private theorem physicalRep : Rep Code.start (fun x => List.ofFn (core (asRow x))) := by
  intro i
  by_cases hi : i < 40
  · exact ⟨mask ⟨i,hi⟩,fun x hx => by simpa only [readFn,dite_eq_left hi,wires] using embeddedBit ⟨i,hi⟩ x hx⟩
  · simpa only [readFn,dite_eq_right hi] using bot (by decide) Code.start

theorem five (reject : ∀ p : Program, ¬ agrees p)
    (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn (core x)) = Row4201.PGHexSequence.cycleAccepts x) :
    5 ≤ C.gates.countP ZeroSensitivity.isOr := by
  by_contra! small
  obtain ⟨p,hp⟩ := smallProgram C hm (by omega) _ (fun _ => by simp) physicalRep
  have eq (x : BitVec 6) (hx : x ≠ 63) : run p x = Row4201.PGHexSequence.cycleAccepts (asRow x) :=
    (hp x hx).trans (hc _)
  apply reject p
  unfold agrees
  repeat' apply And.intro
  all_goals (rw [eq _ (by decide)]; decide)


theorem lower39 (C : Circuit) (hm : Monotone2 C) (correct : ∀ x, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 40, (u.val,v.val) ∈ Upper114.edges ∧ x u = true ∧ x v = true) :
    39 ≤ C.gates.countP Row4201.Charging.isOr := by
  classical
  have eq (x : Fin 40 → Bool) : C.eval (List.ofFn x) = tests x :=
    Bool.eq_iff_iff.mpr ((correct x).trans (literal x).symm)
  let ready (j : Fin C.gates.length) : Prop := Row4201.Charging.isOr C.gates[j] = true ∧
    ∀ w ∈ C.gates[j].inputs, prefixRead C j (pref 0) w = true
  let occupied := Finset.univ.filter ready
  have charges := lowerWithCore C hm 34 pref pair occupied (fun j hj => (Finset.mem_filter.mp hj).2)
    (by intro i j h v hv; simp only [pref,decide_eq_true_eq] at *; omega)
    (by intro k; simpa only [eq] using samples k) witnessNext
  have smaller := Row4201.Restrict.count_toCore_le C hm (pref 0) ready (fun _ a b => ⟨a,b⟩)
  let D := Row4201.Restrict.toCore C (pref 0)
  have bound := five Row4201.HexFour.noFour D (Row4201.Restrict.toCore_mono C hm _) (by
    intro x
    change (Row4201.Restrict.toCore C (pref 0)).eval _ = _
    rw [Row4201.Restrict.eval_toCore _ hm]
    have same : Row4201.Restrict.mask (pref 0) (core x) = core x := by
      funext v
      unfold Row4201.Restrict.mask
      cases h : core x v with
      | false => simp
      | true => simp [marks x v h]
    rw [same,eq,coreValue])
  have sameOr : ZeroSensitivity.isOr = Row4201.Charging.isOr := by
    funext g; cases h : g.op <;> simp [ZeroSensitivity.isOr,Row4201.Charging.isOr,h]
  rw [sameOr] at bound
  exact (Nat.add_le_add_left (bound.trans smaller) 34).trans charges
end Row9802.SixCycle
#print axioms Row9802.SixCycle.lower39
