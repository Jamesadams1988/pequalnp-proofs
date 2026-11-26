import PEqualNP.Outside.L_meta_1500
import PEqualNP.Outside.L_meta_2145

namespace Degree9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def edges : List (ℕ × ℕ) := [(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]

theorem edge_count : edges.length = 51 ∧ edges.Nodup := by decide +kernel

theorem matching : ∀ w : Fin 13, ((w + 1).val, 13 + w.val) ∈ edges := by decide +kernel

theorem common_neighbors : ∀ p q : Fin 13, p ≠ q →
    (Finset.univ.filter (fun w : Fin 13 =>
      (p.val,13+w.val) ∈ edges ∧ (q.val,13+w.val) ∈ edges)).card ≤ 1 := by decide +kernel

def old (x : Fin 26 → Bool) :=
  ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

def hit (p w : Fin 13) := ∃ d : ℕ, d ∈ ({0,1,3,9} : Finset ℕ) ∧ (w.val+d)%13=p.val

def full (x : Fin 26 → Bool) :=
  ∃ p w : Fin 13, hit p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true

private def inc (p w : Fin 13) : Prop := p = w ∨ p = w+1 ∨ p=w+3 ∨ p=w+9
private instance : DecidableRel inc := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
private theorem hit_iff (p w : Fin 13) : hit p w ↔ inc p w := by
  have aux : ∀ a b : Fin 13, ((b.val+0)%13=a.val ∨ (b.val+1)%13=a.val ∨
    (b.val+3)%13=a.val ∨ (b.val+9)%13=a.val) ↔ inc a b := by decide +kernel
  rw [←aux]
  simp only [hit,Finset.mem_insert,Finset.mem_singleton]
  grind

private theorem coord : ∀ u v : Fin 26,
    ((u.val,v.val) ∈ edges ∨ (u=0 ∧ v=13)) ↔
      ∃ p w : Fin 13, inc p w ∧ u=Fin.castAdd 13 p ∧ v=Fin.natAdd 13 w := by decide +kernel

theorem full_iff (x : Fin 26 → Bool) :
    full x ↔ old x ∨ (x 0 = true ∧ x 13 = true) := by
  constructor
  · rintro ⟨p,w,hi,hp,hw⟩
    rcases (coord _ _).2 ⟨p,w,(hit_iff _ _).1 hi,rfl,rfl⟩ with he | ⟨h,k⟩
    · exact Or.inl ⟨_,_,he,hp,hw⟩
    · exact Or.inr ⟨h ▸ hp,k ▸ hw⟩
  · rintro (⟨u,v,he,hu,hv⟩ | ⟨hu,hv⟩)
    · obtain ⟨p,w,h,rfl,rfl⟩ := (coord u v).1 (Or.inl he)
      exact ⟨p,w,(hit_iff _ _).2 h,hu,hv⟩
    · exact ⟨0,0,(hit_iff _ _).2 (by decide),hu,hv⟩

def run {α : Type} (f : Gate → List α → α) (gs : List Gate) (w : List α) :=
  gs.foldl (fun s g => s ++ [f g s]) w

private theorem length_run {α} (f : Gate → List α → α) (gs w) :
    (run f gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run f gs (w++[_])).length = _
    rw [ih]; simp; omega

private theorem keep_run {α} (f : Gate → List α → α) (d : α) (gs w) (i) (hi : i<w.length) :
    (run f gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run f gs (w++[_])).getD i d = _
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i=>w.getD i false)
private def deg (g : Gate) (d : List ℕ) := g.lineDegree d
private def marks (lines : Bool) : Finset ℕ := if lines then Finset.Ico 13 26 else Finset.range 13
private def init (lines : Bool) := (List.range 26).map fun i => if i ∈ marks lines then 1 else 0
private def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩
private def endAt (C : Circuit) := 26+C.gates.length
def fill (C : Circuit) : Circuit :=
  ⟨C.gates ++ [gate .and 0 13, gate .or C.output (endAt C)], endAt C+1⟩

private theorem length_val (C : Circuit) (x : Fin 26 → Bool) :
    (C.wires (List.ofFn x)).length = endAt C := by
  change (run val C.gates (List.ofFn x)).length = _
  simp [length_run,endAt]

private theorem valid {C : Circuit} (h : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ old x) :
    C.output < endAt C := by
  have live := (h (fun _ => true)).2 ⟨0,17,by decide,rfl,rfl⟩
  by_contra! bad
  change (C.wires (List.ofFn (fun _ : Fin 26 => true))).getD C.output false = true at live
  rw [List.getD_eq_default _ _ (by rw [length_val]; exact bad)] at live
  contradiction

private theorem val_inputs (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (run val C.gates (List.ofFn x)).getD i.val false = _
  rw [keep_run _ _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem snoc {α} (d : α) (w : List α) (v : α) :
    (w++[v]).getD w.length d = v := by simp [List.getD]

private theorem keep {α} (d : α) (w : List α) (v : α) {i} (hi : i<w.length) :
    (w++[v]).getD i d = w.getD i d := by simp [List.getD,List.getElem?_append_left hi]

theorem fill_eval (C : Circuit) (validOut : C.output < endAt C) (x : Fin 26 → Bool) :
    (fill C).eval (List.ofFn x) = (C.eval (List.ofFn x) || (x 0 && x 13)) := by
  let w := C.wires (List.ofFn x)
  let g := gate .and 0 13
  let z := w ++ [val g w]
  have hlen : w.length = endAt C := length_val C x
  have zlen : z.length = endAt C+1 := by simp [z,hlen]
  have val_g : val g w = (x 0 && x 13) := by
    change (w.getD 0 false && (w.getD 13 false && true)) = _
    have a : w.getD 0 false = x 0 := val_inputs C x 0
    have b : w.getD 13 false = x 13 := val_inputs C x 13
    rw [a,b,Bool.and_true]
  change ((C.gates++[g,gate .or C.output (endAt C)]).foldl (fun s a => s++[val a s])
    (List.ofFn x)).getD (endAt C+1) false = _
  rw [List.foldl_append]
  change (z++[val (gate .or C.output (endAt C)) z]).getD (endAt C+1) false = _
  rw [←zlen,snoc]
  have h₁ : z.getD C.output false = w.getD C.output false := keep _ _ _ (hlen ▸ validOut)
  have h₂ : z.getD (endAt C) false = val g w := hlen ▸ snoc _ _ _
  change (z.getD C.output false || (z.getD (endAt C) false || false)) = _
  rw [h₁,h₂,val_g,Bool.or_false]
  rfl

theorem fill_degree (C : Circuit) (validOut : C.output < endAt C) (s : Bool) :
    (fill C).lineDeg 26 (marks s) = max (C.lineDeg 26 (marks s)) 1 := by
  let w := run deg C.gates (init s)
  let g := gate .and 0 13
  let z := w++[deg g w]
  have hlen : w.length = endAt C := by simp [w,length_run,init,endAt]
  have zlen : z.length = endAt C+1 := by simp [z,hlen]
  have g_val : deg g w = 1 := by
    have a : w.getD 0 0 = (init s).getD 0 0 := keep_run _ _ _ _ _ (by simp [init])
    have b : w.getD 13 0 = (init s).getD 13 0 := keep_run _ _ _ _ _ (by simp [init])
    change (gate .and 0 13).lineDegree w = 1
    simp only [gate,Gate.lineDegree,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,a,b]
    cases s <;> decide
  change ((C.gates++[g,gate .or C.output (endAt C)]).foldl (fun d a=>d++[deg a d])
    (init s)).getD (endAt C+1) 0 = _
  rw [List.foldl_append]
  change (z++[deg (gate .or C.output (endAt C)) z]).getD (endAt C+1) 0 = _
  rw [←zlen,snoc]
  have h₁ : z.getD C.output 0 = w.getD C.output 0 := keep _ _ _ (hlen ▸ validOut)
  have h₂ : z.getD (endAt C) 0 = deg g w := hlen ▸ snoc _ _ _
  change max (z.getD C.output 0) (max (z.getD (endAt C) 0) 0) = _
  rw [h₁,h₂,g_val]
  rfl

private theorem fill_mono {C : Circuit} (h : Monotone2 C) : Monotone2 (fill C) := by
  intro g hg
  simp [fill] at hg
  rcases hg with h₁|h₁|h₁
  · exact h _ h₁
  · subst g; simp [gate]
  · subst g; simp [gate]

private theorem fill_graph (C : Circuit) (h : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ old x)
    (x : Fin 26 → Bool) : (fill C).eval (List.ofFn x) = true ↔ full x := by
  rw [fill_eval C (valid h),full_iff,Bool.or_eq_true,Bool.and_eq_true,h x]

private def OfficialInc := hit
private abbrev fullFn := full
private def pointInc (p w : Fin 13) : Prop :=
  ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d

private theorem convertInc (p w : Fin 13) : OfficialInc p w ↔ pointInc p w := by
  rw [show OfficialInc p w ↔ inc p w from hit_iff p w]
  have allPairs : ∀ a b : Fin 13, inc a b ↔ pointInc a b := by unfold pointInc; decide +kernel
  exact allPairs p w

/-- Exact full plane incidence implies the positive and negative tests of L-meta-2145. -/
theorem point_obstruction (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ fullFn x) :
    63 < C.size ∨ 1 < C.lineDeg 26 (Finset.range 13) := by
  by_contra! small
  rcases small with ⟨size,degree⟩
  apply PEqualNP.Outside.L_meta_2145
  refine ⟨C,mono,size,degree,?_,?_⟩
  · intro p w edge
    apply (correct _).mpr
    refine ⟨p,w,(convertInc p w).mpr edge,?_,?_⟩
    · exact decide_eq_true (Or.inl rfl)
    · exact decide_eq_true (Or.inr rfl)
  · intro S _outside _nonconcurrent
    apply Bool.eq_false_iff.mpr
    intro hx
    obtain ⟨p,w,inc,hp,hw⟩ := (correct _).mp hx
    change decide _ = true at hp hw
    simp only [decide_eq_true_eq] at hp hw
    have sep : ∀ a b : Fin 13, Fin.castAdd 13 a ≠ Fin.natAdd 13 b := by decide +kernel
    have lInj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := by decide +kernel
    have rInj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := by decide +kernel
    obtain ⟨u,mu,eu⟩ | ⟨l,el,_⟩ := hp
    · have ep := lInj eu
      subst u
      obtain ⟨v,_,ev⟩ | ⟨k,ek,indep⟩ := hw
      · exact sep v w ev.symm
      · have ew := rInj ek
        subst k
        exact indep p mu ((convertInc p w).mp inc)
    · exact sep p l el


theorem small_degrees (C : Circuit) (m : Monotone2 C) (hs : C.size ≤ 61)
    (h : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ old x) :
    2 ≤ C.lineDeg 26 (Finset.range 13) ∧ 2 ≤ C.lineDeg 26 (Finset.Ico 13 26) := by
  have size : (fill C).size ≤ 63 := by simp [fill,Circuit.size] at hs ⊢; omega
  have po := point_obstruction (fill C) (fill_mono m) (fill_graph C h)
  have p : 1 < (fill C).lineDeg 26 (marks false) := by rcases po with big|small; omega; exact small
  have l : 1 < (fill C).lineDeg 26 (marks true) := by
    by_contra! deg
    apply PEqualNP.Outside.L_meta_1500
    refine ⟨fill C,fill_mono m,size,deg,?_,?_⟩
    · intro x _ hpos; exact (fill_graph C h x).1 hpos
    · intro p w hi
      exact (fill_graph C h _).2 ⟨p,w,hi,by simp,by simp⟩
  rw [fill_degree C (valid h)] at p l
  simp [marks] at p l
  omega

#print axioms small_degrees
end Degree9742
