import RemainingCases
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace ForestIncidence

private theorem side_ne {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro e
  have h := congrArg Fin.val e
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h
  have := p.isLt
  omega

private theorem left_adj {N : ℕ} {I : Fin N → Fin N → Prop} {p : Fin N} {v : Fin (N+N)}
    (h : (graph I).Adj (Fin.castAdd N p) v) : ∃ l, v = Fin.natAdd N l ∧ I p l := by
  obtain ⟨q,l,i,⟨h1,h2⟩|⟨_,bad⟩⟩ := h
  · have e : p = q := Fin.ext (congrArg (fun z : Fin (N+N) => z.val) h1)
    exact ⟨l,h2,e ▸ i⟩
  · exact False.elim (side_ne _ _ bad)

private theorem right_adj {N : ℕ} {I : Fin N → Fin N → Prop} {l : Fin N} {v : Fin (N+N)}
    (h : (graph I).Adj (Fin.natAdd N l) v) : ∃ p, v = Fin.castAdd N p ∧ I p l := by
  obtain ⟨p,q,i,⟨bad,_⟩|⟨h1,h2⟩⟩ := h
  · exact False.elim (side_ne _ _ bad.symm)
  · have e : l = q := by
      apply Fin.ext
      have k := congrArg Fin.val h2
      simp only [Fin.val_natAdd] at k
      omega
    exact ⟨p,h1,e ▸ i⟩

private theorem from_left {N : ℕ} {I : Fin N → Fin N → Prop} (free : NoRectangle I)
    {p l : Fin N} {c d : Fin (N+N)} (ab : I p l)
    (bc : (graph I).Adj (Fin.natAdd N l) c) (cd : (graph I).Adj c d)
    (da : (graph I).Adj d (Fin.castAdd N p)) (ac : Fin.castAdd N p ≠ c) (bd : Fin.natAdd N l ≠ d) : False := by
  obtain ⟨q,rfl,ql⟩ := right_adj bc
  obtain ⟨k,rfl,qk⟩ := left_adj cd
  obtain ⟨r,eq,pr⟩ := right_adj da
  have pp : p = r := Fin.ext (congrArg (fun z : Fin (N+N) => z.val) eq)
  subst r
  exact free p q l k (fun h => ac (congrArg _ h)) (fun h => bd (congrArg _ h)) ⟨ab,pr,ql,qk⟩

private theorem no_four_walk {N : ℕ} {I : Fin N → Fin N → Prop} (free : NoRectangle I)
    {v : Fin (N+N)} (w : (graph I).Walk v v) (hc : w.IsCycle) (four : w.length = 4) : False := by
  have a := w.adj_getVert_succ (i := 0) (by omega)
  have b := w.adj_getVert_succ (i := 1) (by omega)
  have c := w.adj_getVert_succ (i := 2) (by omega)
  have d := w.adj_getVert_succ (i := 3) (by omega)
  have close : w.getVert 4 = w.getVert 0 := by rw [← four, w.getVert_length, w.getVert_zero]
  change (graph I).Adj (w.getVert 3) (w.getVert 4) at d
  rw [close] at d
  have distinct (i j : ℕ) (hi : i < 4) (hj : j < 4) (hne : i ≠ j) : w.getVert i ≠ w.getVert j := by
    intro eq
    apply hne
    exact hc.getVert_injOn' (show i ≤ w.length-1 by omega) (show j ≤ w.length-1 by omega) eq
  have ac := distinct 0 2 (by decide) (by decide) (by decide)
  have bd := distinct 1 3 (by decide) (by decide) (by decide)
  rcases a with ⟨p,l,i,⟨ha,hb⟩ | ⟨hb,ha⟩⟩
  · exact from_left free i (hb ▸ b) c (ha ▸ d) (ha ▸ ac) (hb ▸ bd)
  · exact from_left free i (ha ▸ d.symm) c.symm (hb ▸ b.symm) (hb ▸ bd) (ha ▸ ac)

private def sideColor {N : ℕ} (I : Fin N → Fin N → Prop) : (graph I).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun u => decide (u.val < N)) (by
    rintro u v ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ <;> simp [Fin.val_castAdd, p.isLt])

theorem short_iff_hexagon {N : ℕ} {I : Fin N → Fin N → Prop} (free : NoRectangle I) :
    ShortCycle I ↔ ∃ v : Fin (N+N), ∃ w : (graph I).Walk v v, w.IsCycle ∧ w.length = 6 := by
  constructor
  · rintro ⟨v,w,hc,short⟩
    have parity := ((sideColor I).even_length_iff_congr w).mpr Iff.rfl
    obtain ⟨k,hk⟩ := parity
    have lo := hc.three_le_length
    have no4 : w.length ≠ 4 := no_four_walk free w hc
    refine ⟨v,w,hc,?_⟩
    omega
  · rintro ⟨v,w,hc,hs⟩
    refine ⟨v,w,hc,?_⟩
    omega

end ForestIncidence
