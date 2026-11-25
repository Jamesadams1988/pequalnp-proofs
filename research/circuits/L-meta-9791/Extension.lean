import PEqualNP.Defs
namespace PartialPlaneExtension
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def remap (i : ℕ) := if i < 13 then i else if i < 24 then i+2 else i+11
def rename (g : Gate) : Gate := ⟨g.op, g.inputs.map remap⟩
def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩
def pre : List Gate :=
  [gate .or 0 1, gate .or 3 9, gate .or 26 27, gate .and 13 28,
   gate .or 1 2, gate .or 4 10, gate .or 30 31, gate .and 14 32,
   gate .or 29 33]
def extension (C : Circuit) : Circuit :=
  ⟨pre ++ C.gates.map rename ++ [gate .or 34 (remap C.output)], 35+C.gates.length⟩
theorem size_extension (C : Circuit) : (extension C).size = C.size+10 := by
  simp [extension,Circuit.size,pre]
theorem mono_extension {C : Circuit} (h : Monotone2 C) : Monotone2 (extension C) := by
  rintro g hg
  simp only [extension, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (h0|⟨a,ha,rfl⟩)|rfl
  · simp [pre] at h0
    rcases h0 with h|h|h|h|h|h|h|h|h <;> subst g <;> simp [gate]
  · simpa [rename] using h a ha
  · simp [gate]

def run {α : Type} (f : GateOp → List α → α) (d : α)
    (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun s g => s++[f g.op (g.inputs.map (fun i => s.getD i d))]) w

theorem run_length {α} (f : GateOp → List α → α) (d : α) (gs w) :
    (run f d gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run,List.foldl_cons,List.length_cons] at *
    rw [ih]; simp; omega

theorem run_keep {α} (f : GateOp → List α → α) (d : α) (gs w) (i) (h:i<w.length) :
    (run f d gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run f d gs (w++[_])).getD i d = _
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

theorem insert_read {α} (d : α) (x y : List α) (k:24 ≤ x.length)
    (sz:y.length=x.length+11) (h : ∀ i, y.getD (remap i) d=x.getD i d)
    (v:α) (i:ℕ) :
    (y++[v]).getD (remap i) d=(x++[v]).getD i d := by
  by_cases hi : i<x.length
  · have hj : remap i < y.length := by unfold remap; split <;> (try split) <;> omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
      List.getElem?_append_left hj] using h i
  · have hr : remap i = i+11 := by simp [remap,show ¬i<13 by omega,show ¬i<24 by omega]
    simp only [List.getD_eq_getElem?_getD,hr,
      List.getElem?_append_right (show y.length ≤ i + 11 by omega),
      List.getElem?_append_right (show x.length ≤ i by omega)]
    rw [show i+11-y.length=i-x.length by omega]

theorem run_rename {α} (f : GateOp → List α → α) (d : α) (gs : List Gate)
    (x y : List α) (k:24≤x.length) (sz:y.length=x.length+11)
    (h : ∀ i, y.getD (remap i) d=x.getD i d) (i) :
    (run f d (gs.map rename) y).getD (remap i) d=(run f d gs x).getD i d := by
  induction gs generalizing x y with
  | nil => exact h i
  | cons g gs ih =>
    change (run f d (gs.map rename) (y++[f g.op ((g.inputs.map remap).map (fun j=>y.getD j d))])).getD _ _ =
      (run f d gs (x++[f g.op (g.inputs.map (fun j=>x.getD j d))])).getD _ _
    have eq : (g.inputs.map remap).map (fun j=>y.getD j d) = g.inputs.map (fun j=>x.getD j d) := by
      rw [List.map_map]; exact List.map_congr_left (fun a _ => h a)
    rw [eq]
    apply ih _ _ (by simp;omega) (by simp; omega)
    exact insert_read d x y k sz h _

def restrict (x : Fin 26 → Bool) (i:Fin 24) : Bool :=
  x ⟨remap i, by have := i.isLt; unfold remap; split <;> omega⟩

def missing (x : Fin 26 → Bool) : Bool :=
  (x 13 && ((x 0 || x 1) || (x 3 || x 9))) ||
  (x 14 && ((x 1 || x 2) || (x 4 || x 10)))

theorem pre_eval (x : Fin 26 → Bool) :
    (run GateOp.eval false pre (List.ofFn x)).getD 34 false = missing x := by
  simp [run,pre,gate,missing,GateOp.eval,List.getD]

theorem start_read (x : Fin 26 → Bool) (i : ℕ) :
    (run GateOp.eval false pre (List.ofFn x)).getD (remap i) false =
      (List.ofFn (restrict x)).getD i false := by
  by_cases hi : i<24
  · have hj : remap i < (List.ofFn x).length := by
      simp only [List.length_ofFn]; unfold remap; split <;> omega
    rw [run_keep _ _ _ _ _ hj]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (show i < (List.ofFn (restrict x)).length by simpa only [List.length_ofFn] using hi)]
    simp only [List.getElem_ofFn, Option.getD_some, restrict]
  · have hr : remap i=i+11 := by simp [remap,hi,show ¬i<13 by omega]
    have hn : (run GateOp.eval false pre (List.ofFn x)).length ≤ i+11 := by
      rw [run_length]; simp [pre]; omega
    simp only [List.getD_eq_getElem?_getD,hr]
    rw [List.getElem?_eq_none hn,List.getElem?_eq_none (show (List.ofFn (restrict x)).length ≤ i by rw [List.length_ofFn];omega)]

theorem extension_out {α} (f : GateOp → List α → α) (d : α) (C : Circuit)
    (old new : List α) (ho : old.length = 24) (hn : new.length = 26)
    (h : ∀ i, (run f d pre new).getD (remap i) d = old.getD i d) :
    (run f d (extension C).gates new).getD (extension C).output d =
    f .or [(run f d pre new).getD 34 d, (run f d C.gates old).getD C.output d] := by
  let first := run f d pre new
  let mid := run f d (C.gates.map rename) first
  have ls : first.length = 35 := by rw [show first = run f d pre new by rfl, run_length, hn]; rfl
  have lm : mid.length = 35 + C.gates.length := by simp only [mid,run_length,List.length_map,ls]
  have e1 : mid.getD 34 d = first.getD 34 d := run_keep _ _ _ _ _ (by omega)
  have e2 : mid.getD (remap C.output) d = (run f d C.gates old).getD C.output d :=
    run_rename f d C.gates old first (by omega) (by omega) h _
  let v := f .or [mid.getD 34 d,mid.getD (remap C.output) d]
  have step : run f d (extension C).gates new = mid ++ [v] := by
    simp [run,extension,gate,List.foldl_append,mid,first,v]
  rw [step,show (extension C).output = mid.length by exact lm.symm]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_concat_length,Option.getD_some]
  change f .or [mid.getD 34 d, mid.getD (remap C.output) d] = _
  rw [e1,e2]
  simp only [first,List.getD_eq_getElem?_getD]

theorem extension_eval (C : Circuit) (x : Fin 26 → Bool) :
    (extension C).eval (List.ofFn x) = (missing x || C.eval (List.ofFn (restrict x))) := by
  change (run GateOp.eval false (extension C).gates (List.ofFn x)).getD (extension C).output false = _
  rw [extension_out GateOp.eval false C (List.ofFn (restrict x)) (List.ofFn x)
    (List.length_ofFn) (List.length_ofFn) (start_read x),pre_eval]
  simp [GateOp.eval, Circuit.eval,Circuit.wires,run]

#print axioms extension_eval
attribute [local instance] lineDegreeGateOpDecEq

def degreeOp (o : GateOp) (vals : List ℕ) :=
  if o = .and then vals.sum else vals.foldr max 0

def marks (n : ℕ) (markLines : Bool) : Finset ℕ :=
  if markLines then Finset.Ico 13 n else Finset.range 13

def initDeg (n : ℕ) (markLines : Bool) :=
  (List.range n).map (fun i => if i ∈ marks n markLines then 1 else 0)

theorem degree_run (C : Circuit) (n : ℕ) (side : Bool) :
    (run degreeOp 0 C.gates (initDeg n side)).getD C.output 0 = C.lineDeg n (marks n side) := by
  rfl

theorem pre_degree (side : Bool) :
    (run degreeOp 0 pre (initDeg 26 side)).getD 34 0 = 1 := by cases side <;> decide

theorem degree_start (side : Bool) (i : ℕ) :
    (run degreeOp 0 pre (initDeg 26 side)).getD (remap i) 0 = (initDeg 24 side).getD i 0 := by
  by_cases hi : i<24
  · have h26 : remap i < (initDeg 26 side).length := by
      simp only [initDeg,List.length_map,List.length_range]
      unfold remap; split <;> omega
    rw [run_keep _ _ _ _ _ h26]
    interval_cases i <;> cases side <;> decide
  · have hr : remap i = i+11 := by simp [remap,hi,show ¬i<13 by omega]
    have hn : (run degreeOp 0 pre (initDeg 26 side)).length ≤ i + 11 := by
      rw [run_length]; simp [initDeg,pre]; omega
    simp only [hr,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hn,List.getElem?_eq_none (show (initDeg 24 side).length ≤ i by simp [initDeg];omega)]

theorem extension_degree (C : Circuit) (side : Bool) :
    (extension C).lineDeg 26 (marks 26 side) = max 1 (C.lineDeg 24 (marks 24 side)) := by
  rw [← degree_run (extension C)]
  rw [extension_out degreeOp 0 C (initDeg 24 side) (initDeg 26 side) (by simp [initDeg])
    (by simp [initDeg]) (degree_start side), pre_degree]
  rw [degree_run]
  simp [degreeOp]

#print axioms extension_degree

def oldEdges : List (ℕ × ℕ) := [(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)]

def OfficialInc (p w : Fin 13) : Prop :=
  ∃ d : ℕ, d ∈ ({0,1,3,9} : Finset ℕ) ∧ (w.val + d) % 13 = p.val

def inc (p w : Fin 13) : Bool :=
  [0,1,3,9].any (fun d : ℕ => decide ((w.val+d)%13 = p.val))

theorem inc_iff (p w : Fin 13) : OfficialInc p w ↔ inc p w = true := by
  simp only [OfficialInc,inc,List.any_eq_true,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_insert,Finset.mem_singleton,decide_eq_true_eq]

def oldFn (x : Fin 24 → Bool) : Prop :=
  ∃ u v : Fin 24, (u.val,v.val) ∈ oldEdges ∧ x u = true ∧ x v = true

def fullFn (x : Fin 26 → Bool) : Prop :=
  ∃ p w : Fin 13, OfficialInc p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true

theorem decode : ∀ p w : Fin 13, inc p w = true ↔
    ((w = 0 ∧ (p=0 ∨ p=1 ∨ p=3 ∨ p=9)) ∨
    (w=1 ∧ (p=1 ∨ p=2 ∨ p=4 ∨ p=10)) ∨
    (2 ≤ w.val ∧ (p.val,w.val+11) ∈ oldEdges)) := by decide

theorem old_shape : ∀ a b : Fin 24, (a.val,b.val) ∈ oldEdges →
    a.val < 13 ∧ 13 ≤ b.val := by decide

theorem input_proj_pt (x : Fin 26 → Bool) (a : Fin 24) (h : a.val<13) :
    restrict x a = x (Fin.castAdd 13 (⟨a.val,h⟩ : Fin 13)) := by
  unfold restrict; congr 1; apply Fin.ext; simp [remap,h]

theorem input_proj_ln (x : Fin 26 → Bool) (b : Fin 24) (h : 13≤b.val) :
    restrict x b = x (Fin.natAdd 13 (⟨b.val-11,by have := b.isLt; omega⟩ : Fin 13)) := by
  unfold restrict; congr 1; apply Fin.ext; simp [remap,show ¬b.val<13 by omega,b.isLt]; omega

theorem extension_graph (C : Circuit) (correct : ∀ z : Fin 24 → Bool,
    C.eval (List.ofFn z) = true ↔ oldFn z) (x : Fin 26 → Bool) :
    (extension C).eval (List.ofFn x) = true ↔ fullFn x := by
  rw [extension_eval,Bool.or_eq_true,correct]
  constructor
  · rintro (extra|⟨a,b,edge,pa,lb⟩)
    · simp only [missing,Bool.or_eq_true,Bool.and_eq_true] at extra
      rcases extra with ⟨hw,(hp|hp)|(hp|hp)⟩|⟨hw,(hp|hp)|(hp|hp)⟩
      · exact ⟨0,0,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨1,0,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨3,0,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨9,0,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨1,1,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨2,1,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨4,1,(inc_iff _ _).mpr (by decide),hp,hw⟩
      · exact ⟨10,1,(inc_iff _ _).mpr (by decide),hp,hw⟩
    · obtain ⟨ha,hb⟩ := old_shape a b edge
      rw [input_proj_pt x a ha] at pa
      rw [input_proj_ln x b hb] at lb
      let p : Fin 13 := ⟨a.val,ha⟩
      let w : Fin 13 := ⟨b.val-11,by have := b.isLt;omega⟩
      refine ⟨p,w,(inc_iff _ _).mpr ((decode _ _).mpr (Or.inr (Or.inr ⟨?_,?_⟩))),pa,lb⟩
      · change 2 ≤ b.val-11; omega
      · change (a.val,b.val-11+11) ∈ oldEdges
        simpa only [Nat.sub_add_cancel (show 11 ≤ b.val by omega)] using edge
  · rintro ⟨p,w,edge,hp,hw⟩
    rcases (decode p w).mp ((inc_iff _ _).mp edge) with ⟨rfl,h⟩|⟨rfl,h⟩|⟨ge,h⟩
    · left; rcases h with rfl|rfl|rfl|rfl <;> simp_all [missing]
    · left; rcases h with rfl|rfl|rfl|rfl <;> simp_all [missing]
    · right
      let a : Fin 24 := ⟨p.val,by have := p.isLt;omega⟩
      let b : Fin 24 := ⟨w.val+11,by have := w.isLt;omega⟩
      refine ⟨a,b,h,?_,?_⟩
      · rw [input_proj_pt x a (show a.val<13 from p.isLt)]; exact hp
      · rw [input_proj_ln x b (show 13≤b.val by change 13≤w.val+11;omega)]
        convert hw using 2
        apply Fin.ext; change 13+(w.val+11-11)=13+w.val; omega

#print axioms extension_graph
end PartialPlaneExtension
