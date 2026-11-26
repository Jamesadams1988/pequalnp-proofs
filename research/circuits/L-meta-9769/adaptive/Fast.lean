import Graph
namespace ProjectiveEdge.Fast
open ProjectiveEdge.Adaptive ProjectiveEdge.Instance Finset
abbrev Fv := Fin 42
private theorem adjLt : ∀ i : Fv, adj i < 2^42 := by decide +kernel

theorem neighTest (s : ℕ) (i : Fv) : (s &&& adj i) ≠ 0 ↔ ∃ j ∈ members s, graph.Adj i j := by
  constructor
  · intro h
    have b := Nat.testBit_log2 h
    have lt : (s &&& adj i).log2 < 42 := (Nat.log2_lt h).mpr
      (Nat.lt_of_le_of_lt Nat.and_le_right (adjLt i))
    rw [Nat.testBit_land] at b
    exact ⟨⟨_,lt⟩,mem_filter.mpr ⟨mem_univ _,(Bool.and_eq_true_iff.mp b).1⟩,(Bool.and_eq_true_iff.mp b).2⟩
  · rintro ⟨j,hj,hij⟩ z
    have b : (s &&& adj i).testBit j.val = true := by rw [Nat.testBit_land]; exact Bool.and_eq_true_iff.mpr ⟨(mem_filter.mp hj).2,hij⟩
    simp [z] at b

private theorem mem_bit (s : ℕ) (i : Fv) : i ∈ members s ↔ s.testBit i.val = true := by simp [members]
private theorem maskErase (s z : ℕ) (v : Fv)
    (h : ∀ i : Fv, z.testBit i.val = (s.testBit i.val && decide (i ≠ v))) : members z = (members s).erase v := by
  ext i
  rw [mem_erase,mem_bit z i,mem_bit s i,h i]
  simp [and_comm]
private theorem maskDiff (a b c : ℕ)
    (h : ∀ i : Fv, c.testBit i.val = (a.testBit i.val && !b.testBit i.val)) : members c = members a \ members b := by
  ext i
  rw [mem_sdiff,mem_bit c i,mem_bit a i,mem_bit b i,h i]
  cases b.testBit i.val <;> simp
private theorem maskPrune (a b : ℕ)
    (h : ∀ i : Fv, b.testBit i.val = (a.testBit i.val && decide ((a &&& adj i) ≠ 0))) : members b = prune graph (members a) := by
  ext i
  change i ∈ members b ↔ i ∈ ((members a).filter _)
  rw [mem_filter,mem_bit b i,mem_bit a i,h i,Bool.and_eq_true,decide_eq_true_eq,neighTest]
private theorem maskNbr (s n : ℕ) (v : Fv) (eq : n = (s &&& adj v)) : members n = neighbors graph (members s) v := by
  ext i
  change i ∈ members n ↔ i ∈ ((members s).filter _)
  rw [mem_filter,mem_bit n i,mem_bit s i,eq,Nat.testBit_land,Bool.and_eq_true]
  rfl

theorem fastLeaf (s k : ℕ) (h : ∀ i : Fv, s.testBit i.val → (s &&& adj i) ≠ 0)
    (size : k+1 ≤ (members s).card) : Bound graph (members s) k := by
  exact leaf (fun i hi => (neighTest _ _).mp (h i ((mem_bit _ _).mp hi))) size

theorem fastBranch (s z0 o0 N Z O k kZ kO : ℕ) (v zw ow q : Fv)
    (hp : s.testBit v.val) (pn : N = (s &&& adj v)) (pq : N.testBit q.val)
    (erase : ∀ i : Fv, z0.testBit i.val = (s.testBit i.val && decide (i ≠ v)))
    (del : ∀ i : Fv, o0.testBit i.val = (z0.testBit i.val && !N.testBit i.val))
    (zc : ∀ i : Fv, Z.testBit i.val = (z0.testBit i.val && decide ((z0 &&& adj i) ≠ 0)))
    (oc : ∀ i : Fv, O.testBit i.val = (o0.testBit i.val && decide ((o0 &&& adj i) ≠ 0)))
    (ze : Z.testBit zw.val ∧ (Z &&& adj zw) ≠ 0) (oe : O.testBit ow.val ∧ (O &&& adj ow) ≠ 0)
    (zb : k ≤ kZ+2) (ob : k ≤ kO+2+(members N).card)
    (zchild : Bound graph (members Z) kZ) (ochild : Bound graph (members O) kO) : Bound graph (members s) k := by
  have ne := maskNbr s N v pn
  have qn := (mem_bit _ _).mpr pq
  rw [ne] at qn
  have er := maskErase _ _ _ erase
  have di := maskDiff _ _ _ del
  have z := maskPrune _ _ zc
  have o := maskPrune _ _ oc
  rw [er] at z
  rw [di,er] at o
  exact branch ((mem_bit _ _).mpr hp) ⟨q,(mem_filter.mp qn).1,(mem_filter.mp qn).2⟩ ne z o
    ⟨zw,(mem_bit _ _).mpr ze.1,(neighTest _ _).mp ze.2⟩ ⟨ow,(mem_bit _ _).mpr oe.1,(neighTest _ _).mp oe.2⟩ zb ob zchild ochild
end ProjectiveEdge.Fast
