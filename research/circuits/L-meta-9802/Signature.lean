import PEqualNP.Defs.MetaComplexityLgpMono

namespace Row9802.Signature
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One choice bit is charged only at a binary AND. -/
def binaryAnd (g : Gate) : Bool :=
  (match g.op with | .and => true | _ => false) && g.inputs.length == 2

private def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)
private def advance (w : List Bool) (g : Gate) := w ++ [value w g]
private def first (w : List Bool) (g : Gate) := w.getD (g.inputs.headD 0) false
private def join (a b : List Bool) := List.zipWith (· || ·) a b

private theorem readJoin {a b : List Bool} (h : a.length = b.length) (i : ℕ) :
    (join a b).getD i false = (a.getD i false || b.getD i false) := by
  induction a generalizing b i with
  | nil => cases b <;> simp_all [join]
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      have len : as.length = bs.length := by simpa using h
      cases i with
      | zero => rfl
      | succ i => exact ih len i

private def bits : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w => if binaryAnd g then first w g :: bits gs (advance w g) else bits gs (advance w g)

private theorem bitsLength (gs : List Gate) (w : List Bool) : (bits gs w).length = gs.countP binaryAnd := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => cases e : binaryAnd g <;> simp [bits,e,ih]

private theorem gateJoin {a b : List Bool} (len : a.length = b.length) (g : Gate)
    (mono : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) (arity : g.inputs.length ≤ 2)
    (same : binaryAnd g = true → first a g = first b g) :
    value (join a b) g = (value a g || value b g) := by
  rcases g with ⟨op,ins⟩
  change op = .and ∨ op = .or at mono
  rcases mono with rfl | rfl <;> cases ins with
  | nil => rfl
  | cons i tail =>
    cases tail with
    | nil => simpa [value,GateOp.eval] using readJoin len i
    | cons j tail =>
      cases tail with
      | nil =>
        simp only [value,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
          List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false,readJoin len]
        first
          | have hi := same rfl
            change a.getD i false = b.getD i false at hi
            rw [hi]
            cases b.getD i false <;> simp
          | simp [Bool.or_assoc,Bool.or_left_comm]
      | cons z zs => simp at arity

private theorem wiresLength (gs : List Gate) (w : List Bool) :
    (gs.foldl advance w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,advance,Nat.add_comm,Nat.add_left_comm]

private theorem sameRun (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (same : bits gs a = bits gs b) :
    gs.foldl advance (join a b) = join (gs.foldl advance a) (gs.foldl advance b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have h := mono g (by simp)
    have head : binaryAnd g = true → first a g = first b g := by
      intro hg
      exact (List.cons.inj (by simpa [bits,hg] using same)).1
    have tail : bits gs (advance a g) = bits gs (advance b g) := by
      cases hg : binaryAnd g with
      | false => simpa [bits,hg] using same
      | true => exact (List.cons.inj (by simpa [bits,hg] using same)).2
    have step : advance (join a b) g = join (advance a g) (advance b g) := by
      simpa [advance,join,List.zipWith_append len] using gateJoin len g h.1 h.2 head
    simp only [List.foldl_cons,step]
    exact ih _ _ (by simp [advance,len]) (fun z hz => mono z (by simp [hz])) tail

private theorem joinInput {n} (a b : Fin n → Bool) :
    List.ofFn (fun i => a i || b i) = join (List.ofFn a) (List.ofFn b) := by
  apply List.ext_getElem
  · simp [join]
  · intro i h1 h2
    simp [join]

/-- Different false assignments whose union evaluates to true require different binary-AND signatures. -/
theorem familyBound (C : Circuit) (hm : Monotone2 C) {n} {ι : Type} [Fintype ι]
    (x : ι → Fin n → Bool) (off : ∀ i, C.eval (List.ofFn (x i)) = false)
    (cross : ∀ i j, i ≠ j → C.eval (List.ofFn (fun v => x i v || x j v)) = true) :
    Fintype.card ι ≤ 2 ^ C.gates.countP binaryAnd := by
  let f (i : ι) (v : Fin (C.gates.countP binaryAnd)) : Bool :=
    (bits C.gates (List.ofFn (x i)))[v.val]'(by simp [bitsLength])
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have sig : bits C.gates (List.ofFn (x i)) = bits C.gates (List.ofFn (x j)) := by
      apply List.ext_getElem (by simp [bitsLength])
      intro v h1 _
      exact congrFun eq ⟨v,by simpa [bitsLength] using h1⟩
    have run := sameRun C.gates (List.ofFn (x i)) (List.ofFn (x j)) (by simp) hm sig
    have mismatch := cross i j ne
    rw [joinInput] at mismatch
    change (C.gates.foldl advance _).getD C.output false = true at mismatch
    rw [run, readJoin (by simp [wiresLength])] at mismatch
    change (C.eval (List.ofFn (x i)) || C.eval (List.ofFn (x j))) = true at mismatch
    simp [off] at mismatch
  simpa using Fintype.card_le_of_injective f inj

/-- A maximal false input in the coordinatewise ordering. -/
def MaxFalse {n} (C : Circuit) (x : Fin n → Bool) : Prop :=
  C.eval (List.ofFn x) = false ∧
  ∀ z : Fin n → Bool, x ≤ z → C.eval (List.ofFn z) = false → z = x

/-- An arbitrary monotone fan-in-two DAG with `a` binary ANDs has at most `2^a` maximal false inputs. -/
theorem maximalFalseBound (n : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Nat.card {x : Fin n → Bool // MaxFalse C x} ≤ 2 ^ C.gates.countP binaryAnd := by
  classical
  let _ := Fintype.ofFinite {x : Fin n → Bool // MaxFalse C x}
  rw [Nat.card_eq_fintype_card]
  apply familyBound C hm Subtype.val (fun i => i.2.1)
  intro i j ne
  let z := fun v => i.val v || j.val v
  change C.eval (List.ofFn z) = true
  cases h : C.eval (List.ofFn z) with
  | true => rfl
  | false =>
    have li : i.val ≤ z := fun v => by unfold z; cases i.val v <;> cases j.val v <;> simp
    have lj : j.val ≤ z := fun v => by unfold z; cases i.val v <;> cases j.val v <;> simp
    exact (ne (Subtype.ext ((i.2.2 z li h).symm.trans (j.2.2 z lj h)))).elim

end Row9802.Signature
#print axioms Row9802.Signature.familyBound

#print axioms Row9802.Signature.maximalFalseBound
