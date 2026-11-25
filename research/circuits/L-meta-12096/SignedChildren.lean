import SemanticCuts

/-! Signed subexpressions also give read-once subproblems for partial labels. -/
namespace Row12096Signed.SemanticCuts
open Row12096Signed

/-- A signed expression with exactly the prescribed multiset of leaf wires. -/
def realizes (ws : List W) (u : W) : Prop :=
  ∃ t : Tree W, t.leaves.Perm ws ∧ (u = t.value id ∨ u = ~~~(t.value id))

def fits (u yes no : W) : Prop :=
  (∀ i : Fin 256, yes[i.val] = true → u[i.val] = true) ∧
  (∀ i : Fin 256, no[i.val] = true → u[i.val] = false)

theorem acceptedRealizes (k : ℕ) (ws : List W) (hit : optimized k 0 ws = true) :
    realizes ws goal := by
  have h : optimized k 0 ((ws.map Tree.leaf).map (Tree.value id)) = true := by
    simpa [List.map_map, Function.comp_def, Tree.value] using hit
  obtain ⟨t, ht, perm⟩ := forestReadOnce id k _ h
  refine ⟨t, by simpa [List.flatMap_map, Function.comp_def, Tree.leaves] using perm, ?_⟩
  rcases ht with ht | ht
  · exact .inl ht.symm
  · right; rw [ht, BitVec.not_not]

private theorem realizeSelf (t : Tree W) :
    realizes t.leaves (t.value id) ∧ realizes t.leaves (~~~(t.value id)) :=
  ⟨⟨t, .refl _, .inl rfl⟩, ⟨t, .refl _, .inr rfl⟩⟩

/-- Both factors are themselves read-once expressions on strictly smaller parts. -/
theorem realizesSplit {ws : List W} {u : W} (hs : realizes ws u) (len : 2 ≤ ws.length) :
    ∃ A B : List W, A ≠ [] ∧ B ≠ [] ∧ (A ++ B).Perm ws ∧ ∃ l r : W,
    realizes A l ∧ realizes B r ∧ (u = l &&& r ∨ u = ~~~(l &&& r)) := by
  obtain ⟨t, perm, pol⟩ := hs
  cases t with
  | leaf i =>
    have e := perm.length_eq
    simp [Tree.leaves] at e
    omega
  | gate op a b =>
    refine ⟨a.leaves, b.leaves, leavesNonempty a, leavesNonempty b, perm, ?_⟩
    have ax := realizeSelf a
    have bx := realizeSelf b
    cases op with
    | both => exact ⟨_, _, ax.1, bx.1, pol⟩
    | either =>
      refine ⟨_, _, ax.2, bx.2, ?_⟩
      change u = a.value id ||| b.value id ∨ u = ~~~(a.value id ||| b.value id) at pol
      rw [← BitVec.not_or, BitVec.not_not]
      exact pol.symm
    | leftOnly => exact ⟨_, _, ax.1, bx.2, pol⟩
    | rightOnly =>
      refine ⟨_, _, ax.2, bx.1, ?_⟩
      rw [BitVec.and_comm]
      exact pol

/-- After choosing l, the second child must reject precisely the negative points on which l is true. -/
theorem andMatches (l r yes no : W) :
    fits (l &&& r) yes no ↔ fits l yes 0 ∧ fits r yes (no &&& l) := by
  constructor
  · rintro ⟨p,n⟩
    refine ⟨⟨fun i hi => ?_, by simp⟩, fun i hi => ?_, fun i hi => ?_⟩
    · have eq := p i hi
      simp only [BitVec.getElem_and, Bool.and_eq_true] at eq
      exact eq.1
    · have eq := p i hi
      simp only [BitVec.getElem_and, Bool.and_eq_true] at eq
      exact eq.2
    · simp only [BitVec.getElem_and, Bool.and_eq_true] at hi
      simpa only [BitVec.getElem_and, hi.2, Bool.true_and] using n i hi.1
  · rintro ⟨⟨p,_⟩, q,n⟩
    constructor
    · intro i hi
      simp only [BitVec.getElem_and, p i hi, q i hi, Bool.true_and]
    · intro i hi
      cases h : l[i.val] with
      | false => simp [h]
      | true => simp [h, n i (by simp [hi,h])]

theorem notMatches (u yes no : W) : fits (~~~u) yes no ↔ fits u no yes := by
  unfold fits
  simp only [BitVec.getElem_not, Bool.not_eq_true', Bool.not_eq_false']
  exact and_comm

/-- Necessary recursive subproblems for either orientation of the last signed gate. -/
theorem partialSplit {ws : List W} {u yes no : W} (hs : realizes ws u)
    (hit : fits u yes no) (len : 2 ≤ ws.length) :
    ∃ A B : List W, A ≠ [] ∧ B ≠ [] ∧ (A ++ B).Perm ws ∧ ∃ l r : W,
    realizes A l ∧ realizes B r ∧
    ((fits l yes 0 ∧ fits r yes (no &&& l)) ∨
     (fits l no 0 ∧ fits r no (yes &&& l))) := by
  obtain ⟨A,B,ha,hb,p,l,r,hl,hr,pol⟩ := realizesSplit hs len
  refine ⟨A,B,ha,hb,p,l,r,hl,hr,?_⟩
  rcases pol with rfl | rfl
  · exact .inl ((andMatches ..).mp hit)
  · exact .inr ((andMatches ..).mp ((notMatches ..).mp hit))

#print axioms acceptedRealizes
#print axioms partialSplit
end Row12096Signed.SemanticCuts
