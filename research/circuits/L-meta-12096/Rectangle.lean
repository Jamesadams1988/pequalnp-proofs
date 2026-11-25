import SignedFrontier

namespace Row12096Rectangle
open Row12096Signed

abbrev Point := Fin 256
abbrev Triple := Point × Point × Point

def depends (ws : List W) (u : W) : Prop :=
  ∀ i j : Point, (∀ w ∈ ws, w[i.val] = w[j.val]) → u[i.val] = u[j.val]

/-- x has output zero; y and z have output one. The left factor cannot
distinguish x from y and the right factor cannot distinguish x from z. -/
def blocks (g : W) (A B : List W) (t : Triple) : Bool :=
  let (x,y,z) := t
  !g[x.val] && g[y.val] && g[z.val] &&
    A.all (fun w => w[x.val] == w[y.val]) && B.all (fun w => w[x.val] == w[z.val])

theorem blocks_sound {g u v : W} {A B : List W} {t : Triple}
    (b : blocks g A B t = true) (du : depends A u) (dv : depends B v) : g ≠ u &&& v := by
  obtain ⟨x,y,z⟩ := t
  simp only [blocks, Bool.and_eq_true, Bool.not_eq_true'] at b
  obtain ⟨⟨⟨⟨hx,hy⟩,hz⟩, hA⟩,hB⟩ := b
  have hu := du x y (fun w hw => beq_iff_eq.mp (List.all_eq_true.mp hA w hw))
  have hv := dv x z (fun w hw => beq_iff_eq.mp (List.all_eq_true.mp hB w hw))
  intro eq
  subst g
  simp only [BitVec.getElem_and, Bool.and_eq_true] at hx hy hz
  rw [hu, hv, hy.1, hz.2] at hx
  contradiction

def partitions : List W → List (List W × List W)
  | [] => [([],[])]
  | w :: ws => (partitions ws).flatMap fun (A,B) => [(w::A,B),(A,w::B)]

theorem partitions_complete {ws A B : List W} (h : (A ++ B).Perm ws) :
    ∃ p ∈ partitions ws, p.1.Perm A ∧ p.2.Perm B := by
  induction ws generalizing A B with
  | nil =>
    have he := h.length_eq
    simp only [List.length_append, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨([],[]), by simp [partitions], .refl _, .refl _⟩
  | cons w ws ih =>
    have hm : w ∈ A ++ B := h.mem_iff.mpr (by simp)
    rcases List.mem_append.mp hm with ha | hb
    · have e := List.perm_cons_erase ha
      have ht : (A.erase w ++ B).Perm ws := ((e.append_right B).symm.trans h).cons_inv
      obtain ⟨⟨a,b⟩, hp, ea, eb⟩ := ih ht
      exact ⟨(w::a,b), List.mem_flatMap.mpr ⟨(a,b), hp, by simp⟩, (ea.cons w).trans e.symm, eb⟩
    · have e := List.perm_cons_erase hb
      have h' : (w :: (A ++ B.erase w)).Perm (A ++ B) :=
        List.perm_middle.symm.trans (e.symm.append_left A)
      obtain ⟨⟨a,b⟩, hp, ea, eb⟩ := ih (h'.trans h).cons_inv
      exact ⟨(a,w::b), List.mem_flatMap.mpr ⟨(a,b), hp, by simp⟩, ea, (eb.cons w).trans e.symm⟩

def checkAll (ws : List W) (cert : List W → List W → Triple × Triple) : Bool :=
  (partitions ws).all fun (a,b) =>
    a.isEmpty || b.isEmpty || (blocks goal a b (cert a b).1 && blocks (~~~goal) a b (cert a b).2)

/-- The finite certificate excludes every possible AND factorization, for both
output polarities and all nonempty ordered partitions of the original list. -/
theorem excludes_split {ws : List W} {cert} (pass : checkAll ws cert = true)
    (A B : List W) (ha : A ≠ []) (hb : B ≠ []) (partition : (A ++ B).Perm ws)
    (g u v : W) (pol : g = goal ∨ g = ~~~goal) (du : depends A u) (dv : depends B v) :
    g ≠ u &&& v := by
  obtain ⟨⟨a,b⟩, h, ea, eb⟩ := partitions_complete partition
  have qa : a.isEmpty = false := by cases a <;> simp_all
  have qb : b.isEmpty = false := by cases b <;> simp_all
  have raw := List.all_eq_true.mp pass (a,b) h
  simp only [qa, qb, Bool.false_or, Bool.and_eq_true] at raw
  have da : depends a u := fun i j same => du i j (fun w hw => same w (ea.mem_iff.mpr hw))
  have db : depends b v := fun i j same => dv i j (fun w hw => same w (eb.mem_iff.mpr hw))
  rcases pol with rfl | rfl
  · exact blocks_sound raw.1 da db
  · exact blocks_sound raw.2 da db

end Row12096Rectangle
#print axioms Row12096Rectangle.excludes_split
