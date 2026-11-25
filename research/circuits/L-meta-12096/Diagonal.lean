import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_8646

/-! An identification of two inputs computes a known nine-gate function.
If the first gate acts on that pair, the computation also loses that gate.
The nine-gate certificate is willakone's merged L-meta-8646 (PR #12916).
Input relabeling uses Nico Habets's L-meta-4795. -/
namespace Row12096Diagonal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (relabel_size)

def target (x : Fin 6 → Bool) :=
  Nat.testBit (4269866496 * 2^32 + 4261472256)
    (∑ i : Fin 6, if x i then 2^(i : Nat) else 0)

def small (x : Fin 5 → Bool) :=
  Nat.testBit 0xeaa8a888 (PEqualNP.Outside.L_meta_8646_aux.idx5 x)

def left (a : Fin 3) : Fin 6 := ⟨a.val, by omega⟩
def right (b : Bool) : Fin 6 := if b then 5 else 4

def labels (a : Fin 3) (b : Bool) : Fin 6 → Fin 5 :=
  ![1, 2, 3, 0, 1, 4] ∘ Equiv.swap (left a) 0 ∘ Equiv.swap (right b) 4

set_option maxRecDepth 12000 in
theorem image : ∀ a b y, target (y ∘ labels a b) = small y := by decide +kernel

theorem lower (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  have hx := relabel_size (labels 0 false) _ s h
  rw [funext (image 0 false)] at hx
  exact PEqualNP.Outside.L_meta_8646_aux.R0.lb s hx

/-- Re-interpret a circuit suffix with the first gate's output as one
additional input. Any relabeling preserving this first register state
computes the restricted target using only the suffix. -/
theorem dropFirst {n m : ℕ} (g : Gate) (gs : List Gate) (o : ℕ)
    (f : (Fin n → Bool) → Bool) (p : Fin n → Fin m) (q : Fin (n+1) → Fin m)
    (fit : FanInTwo ⟨g :: gs, o⟩)
    (ev : ∀ x, Circuit.eval ⟨g :: gs, o⟩ (List.ofFn x) = f x)
    (step : ∀ y, List.ofFn (y ∘ p) ++
      [g.op.eval (g.inputs.map fun i => (List.ofFn (y ∘ p)).getD i false)] =
        List.ofFn (y ∘ q)) :
    HasCircuitSize m (fun y => f (y ∘ p)) gs.length := by
  let D : Circuit := ⟨gs, o⟩
  let fn (z : Fin (n+1) → Bool) := D.eval (List.ofFn z)
  have cap : HasCircuitSize (n+1) fn gs.length :=
    ⟨D, (fun u hu => fit u (List.mem_cons_of_mem _ hu)), le_rfl, fun _ => rfl⟩
  have reduced := relabel_size q fn gs.length cap
  have eq : (fun y => fn (y ∘ q)) = fun y => f (y ∘ p) := by
    funext y
    change D.eval (List.ofFn (y ∘ q)) = f (y ∘ p)
    rw [← step y]
    exact ev (y ∘ p)
  rwa [eq] at reduced

def gate (a : Fin 3) (b op rev : Bool) : Gate :=
  ⟨if op then .and else .or,
   if rev then [(right b).val, (left a).val] else [(left a).val, (right b).val]⟩

def suffixLabels (a : Fin 3) (b : Bool) : Fin 7 → Fin 5 := Fin.snoc (labels a b) 1

set_option maxRecDepth 16000 in
theorem first_simplifies : ∀ a b op rev (y : Fin 5 → Bool),
    List.ofFn (y ∘ labels a b) ++ [(gate a b op rev).op.eval
      ((gate a b op rev).inputs.map fun i => (List.ofFn (y ∘ labels a b)).getD i false)] =
      List.ofFn (y ∘ suffixLabels a b) := by decide +kernel

theorem cross_gate_lower (a : Fin 3) (b op rev : Bool) (gs : List Gate) (o : ℕ)
    (fit : FanInTwo ⟨gate a b op rev :: gs, o⟩)
    (ev : ∀ x, Circuit.eval ⟨gate a b op rev :: gs, o⟩ (List.ofFn x) = target x) :
    10 ≤ (gate a b op rev :: gs).length := by
  have h := dropFirst _ gs o target (labels a b) (suffixLabels a b) fit ev
    (first_simplifies a b op rev)
  rw [funext (image a b)] at h
  have h9 := PEqualNP.Outside.L_meta_8646_aux.R0.lb _ h
  simpa using Nat.succ_le_succ h9

end Row12096Diagonal
#print axioms Row12096Diagonal.cross_gate_lower
