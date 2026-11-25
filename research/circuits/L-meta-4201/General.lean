import PEqualNP.Defs

/-! Normal form on any family of tests for the official AND/OR evaluator.
Each physical OR appends one generator. All other wire signatures are finite
meets of the available generators, including the false signature for absent wires. -/
namespace FreeMeetNormal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {T : Type}

abbrev Sig (T : Type) := T → Bool

/-- A wire equals the conjunction of some subset of the generator signatures.
The empty subset denotes true. -/
def Selected (bank : Set (Sig T)) (f : Sig T) : Prop :=
  ∃ s : Finset (Sig T), (∀ q ∈ s, q ∈ bank) ∧ ∀ x, f x = true ↔ ∀ q ∈ s, q x = true

inductive Bank (base : Set (Sig T)) : ℕ → Set (Sig T) → Prop where
  | start : Bank base 0 base
  | push {k bank} (old : Bank base k bank) {a b : Sig T} (left : Selected bank a)
      (right : Selected bank b) : Bank base (k+1) (insert (fun x => a x || b x) bank)

private theorem literal {s : Set (Sig T)} {f} (mem : f ∈ s) : Selected s f := by
  classical
  exact ⟨{f}, by simpa, by simp⟩

private theorem weaken {a b : Set (Sig T)} {f} (sub : a ⊆ b) (h : Selected a f) : Selected b f := by
  obtain ⟨s,hs,he⟩ := h
  exact ⟨s,fun q hq => sub (hs q hq),he⟩

private theorem top (s : Set (Sig T)) : Selected s (fun _ => true) := by
  exact ⟨∅,by simp,by simp⟩

private theorem both {s : Set (Sig T)} {f g} (h : Selected s f) (k : Selected s g) :
    Selected s (fun x => f x && g x) := by
  classical
  obtain ⟨a,ha,ea⟩ := h
  obtain ⟨b,hb,eb⟩ := k
  refine ⟨a ∪ b,fun q hq => (Finset.mem_union.mp hq).elim (ha q) (hb q),fun x => ?_⟩
  simp [ea x,eb x]
  exact ⟨fun h q hq => hq.elim (h.1 q) (h.2 q),
    fun h => ⟨fun q hq => h q (.inl hq), fun q hq => h q (.inr hq)⟩⟩

private def gval (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def appendGate (w : List Bool) (g : Gate) := w ++ [gval w g]

def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false

def represents (s : Set (Sig T)) (w : T → List Bool) := ∀ i, Selected s (fun x => (w x).getD i false)

private theorem snocRead (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.getD_cons_succ] using ih i

private theorem update {s : Set (Sig T)} {w : T → List Bool} {n : ℕ} (length : ∀ t, (w t).length = n)
    (repr : represents s w) {g : Gate} (v : Selected s (fun t => gval (w t) g)) :
    represents s (fun t => appendGate (w t) g) := by
  intro i
  by_cases hi : i=n
  · simpa only [appendGate,snocRead,length,ite_eq_left hi] using v
  · simpa only [appendGate,snocRead,length,ite_eq_right hi] using repr i

private theorem ands {s : Set (Sig T)} {w : T → List Bool} (rep : represents s w) (ins : List ℕ) :
    Selected s (fun t => (ins.map (fun i => (w t).getD i false)).all id) := by
  induction ins with
  | nil => simpa using top s
  | cons i ins ih => simpa using both (rep i) ih

private def arg (w : List Bool) : Option ℕ → Bool
  | none => false
  | some i => w.getD i false

private theorem orEq {g : Gate} (ho : g.op = .or) (arity : g.inputs.length ≤ 2) (w : List Bool) :
    gval w g = (arg w g.inputs[0]? || arg w g.inputs[1]?) := by
  rcases g with ⟨op,ins⟩
  obtain rfl : op = GateOp.or := ho
  cases ins with
  | nil => rfl
  | cons i ins =>
    cases ins with
    | nil => simp [gval,arg,GateOp.eval]
    | cons j ins =>
      cases ins with
      | nil => simp [gval,arg,GateOp.eval]
      | cons u us => simp at arity

private theorem repArg {s : Set (Sig T)} {w : T → List Bool} (rep : represents s w)
    (bot : Selected s (fun _ => false)) (id : Option ℕ) :
    Selected s (fun t => arg (w t) id) := by
  cases id with
  | none => exact bot
  | some i => exact rep i

private theorem foldNormal {base s : Set (Sig T)} {k : ℕ} (bank : Bank base k s) (gs : List Gate)
    (ops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    {w : T → List Bool} {n : ℕ} (len : ∀ t, (w t).length=n) (rep : represents s w)
    (bot : Selected s (fun _ => false)) :
    ∃ (j : ℕ) (u : Set (Sig T)), j=k+gs.countP isOr ∧ Bank base j u ∧
      represents u (fun t => gs.foldl appendGate (w t)) := by
  induction gs generalizing k s w n with
  | nil => exact ⟨k,s,rfl,bank,rep⟩
  | cons g gs ih =>
    have tail := fun q (hq : q ∈ gs) => ops q (List.mem_cons_of_mem g hq)
    obtain ⟨op,arity⟩ := ops g List.mem_cons_self
    have len' (x) : (appendGate (w x) g).length = n+1 := by simp [appendGate,len]
    rcases op with ha | ho
    · have cnt : (g::gs).countP isOr = gs.countP isOr := by simp [isOr,ha]
      have v : Selected s (fun x => gval (w x) g) := by simpa [gval,ha,GateOp.eval] using ands rep g.inputs
      rw [cnt]
      exact ih bank tail len' (update len rep v) bot
    · have cnt : (g::gs).countP isOr = gs.countP isOr + 1 := by simp [isOr,ho]
      let a := fun x => arg (w x) g.inputs[0]?
      let b := fun x => arg (w x) g.inputs[1]?
      let z := fun x => a x || b x
      let next := insert z s
      have ext : Bank base (k+1) next := Bank.push bank (repArg rep bot _) (repArg rep bot _)
      have sub : s ⊆ next := Set.subset_insert _ _
      have lifted : represents next w := fun i => weaken sub (rep i)
      have v : Selected next (fun t => gval (w t) g) := by
        simpa only [orEq ho arity] using (literal (Set.mem_insert z s) : Selected next z)
      obtain ⟨j,u,hj,history,result⟩ := ih ext tail len' (update len lifted v) (weaken sub bot)
      exact ⟨j,u,by omega,history,result⟩

/-- From any test family and any supported initial bank, recover a chronological
sequence of exactly the physical OR count. Every final wire is a subset meet. -/
theorem normalize (C : Circuit) (hm : Monotone2 C) (tests : T → Fin n → Bool)
    (base : Set (Sig T)) (inputs : ∀ i, Selected base (fun t => tests t i))
    (zero : Selected base (fun _ => false)) :
    ∃ s : Set (Sig T), Bank base (C.gates.countP isOr) s ∧
      represents s (fun t => C.wires (List.ofFn (tests t))) := by
  have rep : represents base (fun t => List.ofFn (tests t)) := by
    intro i
    by_cases hi : i<n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi]
        using inputs ⟨i,hi⟩
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi]
        using zero
  obtain ⟨j,s,hj,bank,all⟩ := foldNormal (.start (base := base)) C.gates hm
    (fun t => List.length_ofFn (f := tests t)) rep zero
  exact ⟨s,by simpa [hj] using bank,all⟩

/-- The default false generator handles out-of-range reads on arbitrary tests,
including the all-true test. If false is already a meet of input signatures,
`normalize` uses the input signatures alone. -/
theorem physicalNormal (C : Circuit) (hm : Monotone2 C) (tests : T → Fin n → Bool) :
    ∃ s : Set (Sig T),
      Bank (insert (fun _ => false) (Set.range (fun i t => tests t i))) (C.gates.countP isOr) s ∧
      represents s (fun t => C.wires (List.ofFn (tests t))) :=
  normalize C hm tests _ (fun i => literal (Set.mem_insert_of_mem _ ⟨i,rfl⟩))
    (literal (Set.mem_insert _ _))

end FreeMeetNormal
#print axioms FreeMeetNormal.physicalNormal
