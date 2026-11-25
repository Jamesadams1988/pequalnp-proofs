import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.Outside.L_meta_8683

/-!
The table in row 12578 is obtained from the five-input table in row 8683 by
substituting the conjunction of two fresh inputs for its last variable.
The gate saved by fixing one fresh input to true pays for reintroducing that AND.
-/
namespace Split12578.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def CanMono {n} (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

/-- Compute an AND of two input bits on the new wire and run a monotone circuit
whose input map may use that wire any number of times. -/
theorem prepend_and {n m s : ℕ} (f : BFn n) (u v : Fin m) (π : Fin n → Fin (m+1))
    (h : CanMono f s) :
    CanMono (fun x : Fin m → Bool => f (Fin.snoc x (x u && x v) ∘ π)) (s+1) := by
  obtain ⟨C,mono,size,ev⟩ := h
  let g : Gate := ⟨GateOp.and,[u.val,v.val]⟩
  let gs := C.gates.map (relGate n (m+1) π)
  let o := wmap n (m+1) π C.output
  refine ⟨⟨g :: gs,o⟩, ?_, ?_, ?_⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [g]
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      exact ⟨(mono a ha).1, by simpa [relGate] using (mono a ha).2⟩
  · simpa [Circuit.size,gs] using Nat.succ_le_succ size
  · intro x
    let y : Fin (m+1) → Bool := Fin.snoc x (x u && x v)
    have start : step (List.ofFn x) g = List.ofFn y := by
      change step (List.ofFn x) g = List.ofFn (Fin.snoc x (x u && x v) : Fin (m+1) → Bool)
      rw [ofFn_snoc]
      simp [g,step,GateOp.eval]
    change (gs.foldl step (step (List.ofFn x) g)).getD o false = f (y ∘ π)
    rw [start, ← ev (y ∘ π)]
    exact (rel_fold n (m+1) π C.gates _ _ (rel_init n (m+1) π y)).2.2 C.output

def six : BFn 6 := fun x => (4008372968 * 2^32 + 3941133032 : ℕ).testBit (tableIndex x)
def five : BFn 5 := fun x => (0xeeeaeae8 : ℕ).testBit (tableIndex x)
def link : Fin 5 → Fin 7 := ![0,1,2,3,6]

theorem factor : six = fun x => five (Fin.snoc x (x 4 && x 5) ∘ link) := by decide

theorem pin : (fun y : Fin 5 → Bool => six (Fin.snoc y true)) = five := by decide

private theorem depends (p : Fin 6) (hp : p = 4 ∨ p = 5) :
    ∃ x : Fin 6 → Bool, six (Function.update x p (!x p)) ≠ six x := by
  rcases hp with rfl | rfl <;> decide

/-- An arbitrary six-input circuit loses at least one gate on restriction to the five-input table. -/
theorem reduce {s} (h : HasCircuitSize 6 six s) :
    ∃ t, t+1 ≤ s ∧ HasCircuitSize 5 five t := by
  cases s with
  | zero =>
    have hdep : ∀ i ∈ ({4,5} : Finset (Fin 6)), ∃ x : Fin 6 → Bool,
        six (Function.update x i (!x i)) ≠ six x := by
      intro i hi; exact depends i (by simpa using hi)
    have bound := dep_lower_set 6 six {4,5} hdep 0 h
    norm_num at bound
  | succ t =>
    have hdep := depends (Fin.last 5) (Or.inr rfl)
    have hnc : ∃ y y' : Fin 5 → Bool, six (Fin.snoc y true) ≠ six (Fin.snoc y' true) := by decide
    have h' := gate_elim 5 six true t hdep hnc h
    rw [pin] at h'
    exact ⟨t,le_rfl,h'⟩

/-- For this table, a monotone circuit exists at every unrestricted size bound. -/
theorem positive : ∀ s : ℕ, HasCircuitSize 6 six s → CanMono six s := by
  intro s h
  obtain ⟨t,ts,core⟩ := reduce h
  have replaced : CanMono five t := PEqualNP.Outside.L_meta_8683 t core
  obtain ⟨D,dm,ds,de⟩ := prepend_and five 4 5 link replaced
  refine ⟨D,dm,le_trans ds ts,?_⟩
  rw [factor]; exact de

end Split12578.Bridge
