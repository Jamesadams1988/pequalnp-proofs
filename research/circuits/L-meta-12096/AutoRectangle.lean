import ZeroReject

namespace Row12096Rectangle
open Row12096Signed

/-- Positive lanes with the same pattern as x on the selected wires. -/
def agreements (g : W) (x : Point) : List W → W
  | [] => g
  | w :: r => (if w[x.val] then w else ~~~w) &&& agreements g x r

theorem agreements_spec (g : W) (x y : Point) (ws : List W) :
    (agreements g x ws)[y.val] = true ↔
      g[y.val] = true ∧ ∀ w ∈ ws, w[x.val] = w[y.val] := by
  induction ws with
  | nil => simp [agreements]
  | cons w ws ih =>
    simp only [agreements, BitVec.getElem_and, Bool.and_eq_true, ih, List.forall_mem_cons]
    by_cases h : w[x.val] = true <;> by_cases hy : w[y.val] = true <;> simp_all

theorem exists_bit {w : W} (h : (w != 0) = true) : ∃ i : Point, w[i.val] = true := by
  by_contra! bad
  have eq : w = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    simpa using bad ⟨j,hj⟩
  simp [eq] at h

def repRows : List Point := List.ofFn rowPosition
def autoBlock (g : W) (a b : List W) : Bool := repRows.any fun x =>
  !g[x.val] && (agreements g x a != 0) && (agreements g x b != 0)

theorem autoBlock_sound {g : W} {a b : List W} (h : autoBlock g a b = true) :
    ∃ t, blocks g a b t = true := by
  obtain ⟨x, _, hit⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hit
  obtain ⟨⟨hx,ha⟩,hb⟩ := hit
  obtain ⟨y,hy⟩ := exists_bit ha
  obtain ⟨z,hz⟩ := exists_bit hb
  obtain ⟨hgy,hy⟩ := (agreements_spec g x y a).mp hy
  obtain ⟨hgz,hz⟩ := (agreements_spec g x z b).mp hz
  refine ⟨(x,y,z), ?_⟩
  simp only [blocks, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨⟨⟨⟨hx,hgy⟩,hgz⟩,List.all_eq_true.mpr (fun w hw => beq_iff_eq.mpr (hy w hw))⟩,
    List.all_eq_true.mpr (fun w hw => beq_iff_eq.mpr (hz w hw))⟩

def autoCheck (ws : List W) : Bool :=
  (partitions ws).all fun (a,b) =>
    a.isEmpty || b.isEmpty || (autoBlock goal a b && autoBlock (~~~goal) a b)

set_option maxRecDepth 16384 in
theorem autoReject {ws : List W} (h : autoCheck ws = true)
    (k : Nat) (len : 2 ≤ ws.length) : optimized k 0 ws = false := by
  classical
  let choose (g : W) (a b : List W) :=
    if hh : ∃ t, blocks g a b t = true then Classical.choose hh else (0,0,0)
  let cert (a b : List W) : Triple × Triple := (choose goal a b, choose (~~~goal) a b)
  apply rejectZero (cert := cert) _ k len
  apply List.all_eq_true.mpr
  rintro ⟨a,b⟩ p
  have pass := List.all_eq_true.mp h (a,b) p
  by_cases ha : a.isEmpty <;> by_cases hb : b.isEmpty <;> simp_all only [Bool.true_or, Bool.or_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true]
  obtain ⟨l,r⟩ := pass
  have hl := autoBlock_sound l
  have hr := autoBlock_sound r
  have get (g : W) (hh : ∃ t, blocks g a b t = true) : blocks g a b (choose g a b) = true := by
    dsimp only [choose]
    rw [dite_eq_left hh]
    exact Classical.choose_spec hh
  dsimp only [cert]
  exact ⟨get goal hl, get (~~~goal) hr⟩

/-- Run the partition test first, then use the complete zero-slack search
only on unresolved states. -/
def solveZero (k : Nat) (ws : List W) : Bool :=
  if ws.length ≥ 2 && autoCheck ws then false else optimized k 0 ws

theorem solveZero_eq (k : Nat) (ws : List W) : solveZero k ws = optimized k 0 ws := by
  unfold solveZero
  split
  · rename_i h
    obtain ⟨len,chk⟩ := Bool.and_eq_true_iff.mp h
    exact (autoReject chk k (of_decide_eq_true len)).symm
  · rfl

end Row12096Rectangle
#print axioms Row12096Rectangle.solveZero_eq
#print axioms Row12096Rectangle.autoReject
