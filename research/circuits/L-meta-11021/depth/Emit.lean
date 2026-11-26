import TreeBase
import PEqualNP.MetaComplexity.Helpers.Shannon

namespace DepthSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

private theorem past_end (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  rfl

/-- Compile after an arbitrary existing prefix, reserving a globally absent
wire for any out-of-range leaf. Earlier outputs then survive all later gates. -/
private theorem emit {n} (t : Tree n) (good : t.Good) (m reserve : ℕ)
    (start : n ≤ m) (limit : m + t.cost ≤ reserve) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, Ok g) ∧ gs.length = t.cost ∧
      (out < m + gs.length ∨ out = reserve) ∧
      ∀ (x : Fin n → Bool) (w : List Bool), w.length = m →
        (∀ i < n, w.getD i false = (List.ofFn x).getD i false) →
        (wiresFrom gs w).getD out false = t.eval x := by
  induction t generalizing m with
  | leaf i =>
    by_cases hi : i < n
    · refine ⟨[], i, by simp, rfl, Or.inl (by simp; omega), ?_⟩
      intro x w hw hx
      exact hx i hi
    · refine ⟨[], reserve, by simp, rfl, Or.inr rfl, ?_⟩
      intro x w hw _
      change w.getD reserve false = (List.ofFn x).getD i false
      rw [past_end w reserve (by simp [Tree.cost] at limit; omega),
        past_end (List.ofFn x) i (by simp; omega)]
  | node op a b k iha ihb =>
    obtain ⟨op_ok, a_ok, b_ok⟩ := good
    change m + (a.cost + b.cost + 1) ≤ reserve at limit
    obtain ⟨ga, ia, oga, la, ha, ea⟩ := iha a_ok m start (by omega)
    obtain ⟨gb, ib, ogb, lb, _, eb⟩ := ihb b_ok (m+ga.length) (by omega) (by omega)
    let g : Gate := ⟨op, [ia,ib].take k.val⟩
    let idx := m + ga.length + gb.length
    refine ⟨ga ++ gb ++ [g], idx, ?_, ?_, Or.inl ?_, ?_⟩
    · intro gate member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with (h | h) | h
      · exact oga gate h
      · exact ogb gate h
      · subst gate
        exact ⟨op_ok, by simp [g]⟩
    · simp [Tree.cost, la, lb, Nat.add_assoc]
    · simp [idx]; omega
    · intro x w hw hx
      rw [wiresFrom_append, wiresFrom_append]
      let wa := wiresFrom ga w
      let wb := wiresFrom gb wa
      have lwa : wa.length = m + ga.length := by simp [wa, length_wiresFrom, hw]
      have lwb : wb.length = idx := by simp [wb, length_wiresFrom, lwa, idx]
      have in_a : ∀ i < n, wa.getD i false = (List.ofFn x).getD i false := by
        intro i hi
        exact (getD_wiresFrom ga w i (by omega)).trans (hx i hi)
      have va : wb.getD ia false = a.eval x := by
        have eva := ea x w hw hx
        change wa.getD ia false = a.eval x at eva
        rcases ha with h | h
        · exact (getD_wiresFrom gb wa ia (by omega)).trans eva
        · calc
            wb.getD ia false = false := past_end wb ia (by dsimp [idx] at lwb; omega)
            _ = wa.getD ia false := (past_end wa ia (by omega)).symm
            _ = a.eval x := eva
      have vb : wb.getD ib false = b.eval x := eb x wa lwa in_a
      change (wb ++ [op.eval (([ia,ib].take k.val).map (fun j => wb.getD j false))]).getD idx false
        = op.eval ([a.eval x,b.eval x].take k.val)
      rw [← lwb]
      simp only [List.getD_eq_getElem?_getD] at va vb
      simp [List.map_take, va, vb]

theorem Tree.realize {n} (t : Tree n) (h : t.Good) : HasCircuitSize n t.eval t.cost := by
  obtain ⟨gs, out, ok, length, _, eval⟩ :=
    emit t h n (n + t.cost) (by omega) (by omega)
  exact ⟨⟨gs,out⟩, ok, Nat.le_of_eq length, fun x =>
    eval x (List.ofFn x) (by simp) (by intros; rfl)⟩

end DepthSize
