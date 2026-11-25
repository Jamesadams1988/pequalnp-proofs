import Signature
import Upper114
import UnionBlocks

namespace Row9802.MaskFamily
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Row9802.Unions Row9802.Signature Row9802.Upper114

private theorem rowSpec : ∀ u v : Fin 40, (u.val,v.val) ∈ edges ↔
    u.val < 20 ∧ 20 ≤ v.val ∧ (rows.getD u.val 0).testBit (v.val-20) = true := by decide +kernel

private theorem foldSpec (s k j : ℕ) : (foldRows s k).testBit j = true ↔
    ∃ p, p < k ∧ s.testBit p = true ∧ (rows.getD p 0).testBit j = true := by
  induction k with
  | zero => simp [foldRows]
  | succ k ih =>
    rw [foldRows,Nat.testBit_or,Bool.or_eq_true,ih]
    constructor
    · rintro (fresh | ⟨p,hp,hs,hr⟩)
      · by_cases yes : s.testBit k = true
        · exact ⟨k,by omega,yes,by simpa [yes] using fresh⟩
        · simp [yes] at fresh
      · exact ⟨p,by omega,hs,hr⟩
    · rintro ⟨p,hp,hs,hr⟩
      by_cases eq : p = k
      · subst p
        exact .inl (by simpa [hs] using hr)
      · exact .inr ⟨p,by omega,hs,hr⟩

/-- Select the named points and every line that meets none of them. -/
def input (s : ℕ) (v : Fin 40) : Bool :=
  if v.val < 20 then s.testBit v.val else !(hood s).testBit (v.val-20)

private def hasEdge (x : Fin 40 → Bool) :=
  ∃ u v : Fin 40, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

private theorem independent (s : ℕ) : ¬hasEdge (input s) := by
  rintro ⟨u,v,uv,hu,hv⟩
  obtain ⟨pu,lv,edge⟩ := (rowSpec u v).mp uv
  have point : s.testBit u.val = true := by simpa [input,pu] using hu
  have line : (hood s).testBit (v.val-20) = false := by simpa [input,not_lt.mpr lv] using hv
  have yes := (foldSpec s 20 (v.val-20)).mpr ⟨u.val,pu,point,edge⟩
  change (hood s).testBit (v.val-20) = true at yes
  simp_all

private theorem crossBit {s t j : ℕ} (lt : j < 20) (hs : (hood s).testBit j = true)
    (ht : (hood t).testBit j = false) : hasEdge (fun v => input s v || input t v) := by
  obtain ⟨p,hp,point,edge⟩ := (foldSpec s 20 j).mp hs
  let u : Fin 40 := ⟨p,by omega⟩
  let v : Fin 40 := ⟨20+j,by omega⟩
  have hu : input s u = true := by simpa [input,u,hp] using point
  have hv : input t v = true := by simp [input,v,ht]
  exact ⟨u,v,(rowSpec u v).mpr ⟨hp,by simp [v],by simpa [u,v] using edge⟩,
    by simp [hu],by simp [hv]⟩

private theorem cross {s t : ℕ} (hs : hood s < 1048576) (ht : hood t < 1048576)
    (ne : hood s ≠ hood t) : hasEdge (fun v => input s v || input t v) := by
  by_contra h
  apply ne
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases lt : j < 20
  · cases bs : (hood s).testBit j <;> cases bt : (hood t).testBit j
    · rfl
    · exact (h (by simpa only [Bool.or_comm] using crossBit lt bt bs)).elim
    · exact (h (crossBit lt bs bt)).elim
    · rfl
  · have pow : 2^20 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs pow),Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ht pow)]

/-- A block of `n` distinct point-neighborhood unions witnesses `n ≤ 2^a` for the actual 40-input circuit. -/
theorem blockBound {n : ℕ} (b : Block 0 1048576 n) (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x : Fin 40 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 40, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true) :
    n ≤ 2 ^ C.gates.countP binaryAnd := by
  let s (i : Fin n) := b.words[i.val]'(by rw [b.size]; exact i.isLt)
  have has (i : Fin n) : s i ∈ b.words := List.getElem_mem ..
  have inc : StrictMono (fun i : Fin n => hood (s i)) := by
    intro i j ij
    have a := b.ord.rel_getElem_of_lt (i := i.val) (j := j.val)
      (by simp [b.size]) (by simp [b.size]) ij
    simpa [s] using a
  have out := familyBound C hm (fun i : Fin n => input (s i))
    (fun i => by
      cases he : C.eval (List.ofFn (input (s i))) with
      | false => rfl
      | true => exact (independent _ ((computes _).mp he)).elim)
    (fun i j ne => (computes _).mpr (cross (b.bounds _ (has i)).2 (b.bounds _ (has j)).2
      (fun eq => ne (inc.injective eq))))
  simpa using out

end Row9802.MaskFamily
#print axioms Row9802.MaskFamily.blockBound
