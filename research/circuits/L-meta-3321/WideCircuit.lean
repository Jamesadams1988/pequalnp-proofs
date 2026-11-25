import PEqualNP.Defs

namespace WideCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

inductive Kind where | conj | disj

def Kind.op : Kind → GateOp
  | .conj => .and
  | .disj => .or

def Kind.apply : Kind → Bool → Bool → Bool
  | .conj => (· && ·)
  | .disj => (· || ·)

structure Program (n : ℕ) where
  gates : List Gate
  output : ℕ

def Program.asCircuit {n} (p : Program n) : Circuit := ⟨p.gates,p.output⟩
def Program.empty (n) : Program n := ⟨[],0⟩
def Program.values {n} (p : Program n) (x : Fin n → Bool) := p.asCircuit.wires (List.ofFn x)
def Program.wire {n} (p : Program n) (i : ℕ) (x : Fin n → Bool) := (p.values x).getD i false

def Program.push {n} (p : Program n) (k : Kind) (a b : ℕ) : Program n :=
  ⟨p.gates ++ [⟨k.op,[a,b]⟩], n+p.gates.length⟩

theorem push_values {n} (p : Program n) (k : Kind) (a b) (x : Fin n → Bool) :
    (p.push k a b).values x = p.values x ++ [k.apply (p.wire a x) (p.wire b x)] := by
  cases k <;> simp [Program.values, Program.wire, Program.push, Program.asCircuit, Circuit.wires,
    Kind.op, Kind.apply, List.foldl_append, GateOp.eval]

theorem values_prefix {n} (p : Program n) (x : Fin n → Bool) :
    ∃ l : List Bool, p.values x = List.ofFn x ++ l ∧ l.length = p.gates.length := by
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w
  have aux (gs : List Gate) (w : List Bool) :
      ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [a])
      exact ⟨a :: t, by simpa [run, a] using ht, by simp [hl]⟩
  exact aux p.gates (List.ofFn x)

theorem values_length {n} (p : Program n) (x : Fin n → Bool) :
    (p.values x).length = n + p.gates.length := by
  obtain ⟨l, eq, hl⟩ := values_prefix p x
  simp [eq, hl]

theorem raw_wire {n} (p : Program n) (i : Fin n) (x : Fin n → Bool) :
    p.wire i x = x i := by
  obtain ⟨l, eq, _⟩ := values_prefix p x
  simp [Program.wire, eq, List.getElem?_append_left (i := i.val) (by simp : i.val < (List.ofFn x).length)]

theorem push_keeps {n} (p : Program n) (k : Kind) (a b i) (hi : i < n+p.gates.length) (x : Fin n → Bool) :
    (p.push k a b).wire i x = p.wire i x := by
  unfold Program.wire
  rw [push_values, List.getD_append _ _ _ _ (by rwa [values_length])]

theorem push_result {n} (p : Program n) (k : Kind) (a b) (x : Fin n → Bool) :
    (p.push k a b).wire (p.push k a b).output x = k.apply (p.wire a x) (p.wire b x) := by
  change ((p.push k a b).values x).getD (n+p.gates.length) false = _
  rw [push_values, ←values_length p x]
  simp

theorem push_mono {n} (p : Program n) (k : Kind) (a b)
    (hm : Monotone2 p.asCircuit) : Monotone2 (p.push k a b).asCircuit := by
  intro g hg
  change g ∈ p.gates ++ [⟨k.op,[a,b]⟩] at hg
  rcases List.mem_append.mp hg with h | h
  · exact hm g h
  · obtain rfl := List.mem_singleton.mp h
    cases k <;> simp [Kind.op]

theorem push_readsBack {n} (p : Program n) (k : Kind) (a b) (ha : a < n+p.gates.length)
    (hb : b < n+p.gates.length) (h : ReadsBack n p.asCircuit) : ReadsBack n (p.push k a b).asCircuit := by
  intro j hj i hi
  change j < (p.gates ++ ([⟨k.op,[a,b]⟩] : List Gate)).length at hj
  simp only [List.length_append,List.length_cons,List.length_nil] at hj
  by_cases lt : j < p.gates.length
  · apply h j lt i
    simpa [gateAt, Program.asCircuit, Program.push, List.getElem?_append_left lt] using hi
  · have eq : j = p.gates.length := by omega
    subst j
    simp [gateAt, Program.asCircuit, Program.push] at hi
    rcases hi with rfl | rfl <;> assumption

inductive Formula (n : ℕ) where
  | var (i : Fin n)
  | bin (k : Kind) (left right : Formula n)

def Formula.conj {n} (a b : Formula n) := Formula.bin .conj a b
def Formula.disj {n} (a b : Formula n) := Formula.bin .disj a b

def Formula.eval {n} : Formula n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .bin k a b, x => k.apply (a.eval x) (b.eval x)

def Formula.compile {n} : Formula n → Program n → Program n
  | .var i, p => ⟨p.gates,i.val⟩
  | .bin k a b, p =>
    let l := a.compile p
    let r := b.compile l
    r.push k l.output r.output

/-- Every generated gate and the exact subformula computed at its wire, in gate order. -/
def Formula.nodes {n} : Formula n → List (Kind × Formula n)
  | .var _ => []
  | .bin k a b => a.nodes ++ b.nodes ++ [(k, .bin k a b)]

theorem compile_ops {n} (e : Formula n) (p : Program n) :
    ((e.compile p).gates.map Gate.op) = p.gates.map Gate.op ++ e.nodes.map (fun z => z.1.op) := by
  induction e generalizing p with
  | var => simp [Formula.compile, Formula.nodes]
  | bin k a b ia ib => simp [Formula.compile, Program.push, Formula.nodes, ia, ib, List.append_assoc]

theorem compile_size {n} (e : Formula n) (p : Program n) :
    (e.compile p).gates.length = p.gates.length + e.nodes.length := by
  simpa using congrArg List.length (compile_ops e p)

theorem compile_output_lt {n} (e : Formula n) (p : Program n) :
    (e.compile p).output < n+(e.compile p).gates.length := by
  cases e with
  | var i => exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  | bin k a b => simp [Formula.compile, Program.push]

theorem compile_semantics {n} (e : Formula n) (p : Program n) (x : Fin n → Bool) :
    (e.compile p).values x = p.values x ++ e.nodes.map (fun z => z.2.eval x) ∧
    (e.compile p).wire (e.compile p).output x = e.eval x := by
  induction e generalizing p with
  | var i => exact ⟨by simp [Formula.compile,Formula.nodes,Program.values,Program.asCircuit,Circuit.wires], raw_wire p i x⟩
  | bin k a b ia ib =>
    let l := a.compile p
    let r := b.compile l
    have h₁ := ia p
    have h₂ := ib l
    have keep : r.wire l.output x = l.wire l.output x := by
      change ((b.compile l).values x).getD l.output false = _
      rw [h₂.1, List.getD_append _ _ _ _ (by rw [values_length]; exact compile_output_lt a p)]
      rfl
    have left : r.wire l.output x = a.eval x := keep.trans h₁.2
    have right : r.wire r.output x = b.eval x := h₂.2
    constructor
    · change (r.push k l.output r.output).values x = _
      rw [push_values, left, right]
      change (b.compile l).values x ++ _ = _
      rw [h₂.1]
      change (((a.compile p).values x ++ _) ++ _) = _
      rw [h₁.1]
      simp [Formula.nodes, Formula.eval, List.append_assoc]
    · exact (push_result r k l.output r.output x).trans (by rw [left,right]; rfl)

theorem compile_keeps {n} (e : Formula n) (p : Program n) (i : ℕ) (hi : i < n+p.gates.length) (x : Fin n → Bool) :
    (e.compile p).wire i x = p.wire i x := by
  unfold Program.wire
  rw [(compile_semantics e p x).1, List.getD_append _ _ _ _ (by rwa [values_length])]

theorem compile_eval {n} (e : Formula n) (p : Program n) (x : Fin n → Bool) :
    (e.compile p).asCircuit.eval (List.ofFn x) = e.eval x := (compile_semantics e p x).2

theorem compile_mono {n} (e : Formula n) (p : Program n) (h : Monotone2 p.asCircuit) :
    Monotone2 (e.compile p).asCircuit := by
  induction e generalizing p with
  | var => exact h
  | bin k a b ia ib => exact push_mono _ _ _ _ (ib _ (ia _ h))

theorem compile_readsBack {n} (e : Formula n) (p : Program n) (h : ReadsBack n p.asCircuit) :
    ReadsBack n (e.compile p).asCircuit := by
  induction e generalizing p with
  | var => exact h
  | bin k a b ia ib =>
    let l := a.compile p
    have left := compile_output_lt a p
    apply push_readsBack
    · change l.output < n + (b.compile l).gates.length
      rw [compile_size]
      change l.output < n + l.gates.length at left
      omega
    · exact compile_output_lt b l
    · exact ib _ (ia _ h)

/-- Compile from the bare input wires. -/
def circuit {n} (e : Formula n) : Circuit := (e.compile (Program.empty n)).asCircuit

theorem circuit_size {n} (e : Formula n) : (circuit e).gates.length = e.nodes.length := by
  simpa [circuit,Program.asCircuit,Program.empty] using compile_size e (Program.empty n)

theorem circuit_mono {n} (e : Formula n) : Monotone2 (circuit e) := by
  apply compile_mono
  simp [Monotone2, Program.empty, Program.asCircuit]

theorem circuit_reads {n} (e : Formula n) : ReadsBack n (circuit e) := by
  apply compile_readsBack
  simp [ReadsBack, Program.empty, Program.asCircuit]

theorem circuit_eval {n} (e : Formula n) (x : Fin n → Bool) :
    (circuit e).eval (List.ofFn x) = e.eval x := compile_eval _ _ _

theorem circuit_gate {n} (e : Formula n) (j : ℕ) (hj : j < e.nodes.length) :
    (gateAt (circuit e) j).op = e.nodes[j].1.op ∧
    ∀ x : Fin n → Bool, ((circuit e).wires (List.ofFn x)).getD (n+j) false = e.nodes[j].2.eval x := by
  have hgate : j < (e.compile (Program.empty n)).gates.length := by simpa [compile_size,Program.empty] using hj
  have ht := congrArg (fun ops : List GateOp => ops[j]?) (compile_ops e (Program.empty n))
  simp only [Program.empty, List.map_nil, List.nil_append, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some] at ht
  constructor
  · change ((e.compile (Program.empty n)).gates.getD j _).op = _
    rw [List.getD_eq_getElem _ _ hgate]
    change Option.map Gate.op ((e.compile (Program.empty n)).gates[j]?) = some e.nodes[j].1.op at ht
    simpa only [List.getElem?_eq_getElem hgate, Option.map_some, Option.some.injEq] using ht
  · intro x
    change ((e.compile (Program.empty n)).values x).getD (n+j) false = _
    rw [(compile_semantics _ _ _).1]
    change (List.ofFn x ++ _).getD _ false = _
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_map, List.getElem?_eq_getElem hj]

theorem circuit_has_gate {n} (e sub : Formula n) (k : Kind) (present : (k,sub) ∈ e.nodes) :
    ∃ j < (circuit e).gates.length, (gateAt (circuit e) j).op = k.op ∧
      ∀ x : Fin n → Bool, ((circuit e).wires (List.ofFn x)).getD (n+j) false = sub.eval x := by
  obtain ⟨j,hj,heq⟩ := List.getElem_of_mem present
  exact ⟨j, circuit_size e ▸ hj, by simpa only [heq] using circuit_gate e j hj⟩

end WideCircuit
