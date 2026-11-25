import WideCircuit
import WideDefect

namespace WideNet

open WideCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def tailF {n} : (m : ℕ) → (Fin (m+1) → Formula n) → (Fin (m+1) → Formula n) → Formula n
  | 0, _, L => L 0
  | m+1, P, L => (L 0).conj ((P 0).disj (tailF m (fun i => P i.succ) (fun i => L i.succ)))

def diagonalF {n} : (m : ℕ) → (Fin (m+1) → Formula n) → (Fin (m+1) → Formula n) → Formula n
  | 0, P, L => (P 0).conj (L 0)
  | m+1, P, L => ((P 0).conj (L 0)).disj (diagonalF m (fun i => P i.succ) (fun i => L i.succ))

def dirtyF {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) :=
  a.conj (b.disj (tailF m P L))

def outputF {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) :=
  ((dirtyF a b P L).conj b).disj (diagonalF m P L)

theorem eval_tail {n} (m) (P L : Fin (m+1) → Formula n) (x : Fin n → Bool) :
    (tailF m P L).eval x = WideDefect.tail m (fun i => (P i).eval x) (fun i => (L i).eval x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [tailF, Formula.conj, Formula.disj, Formula.eval, Kind.apply, WideDefect.tail, ih]

theorem eval_diagonal {n} (m) (P L : Fin (m+1) → Formula n) (x : Fin n → Bool) :
    (diagonalF m P L).eval x = WideDefect.diagonal (fun i => (P i).eval x) (fun i => (L i).eval x) := by
  induction m with
  | zero => simp [diagonalF, Formula.conj, Formula.eval, Kind.apply, WideDefect.diagonal, List.ofFn_succ]
  | succ m ih =>
    simp only [diagonalF, Formula.disj, Formula.conj, Formula.eval, Kind.apply, ih]
    unfold WideDefect.diagonal
    rw [List.ofFn_succ (f := fun i : Fin (m+1+1) => (P i).eval x && (L i).eval x)]
    rfl

theorem eval_dirty {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) (x : Fin n → Bool) :
    (dirtyF a b P L).eval x = WideDefect.dirty (a.eval x) (b.eval x)
      (fun i => (P i).eval x) (fun i => (L i).eval x) := by
  simp [dirtyF, Formula.conj, Formula.disj, Formula.eval, Kind.apply, eval_tail, WideDefect.dirty]

theorem eval_output {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) (x : Fin n → Bool) :
    (outputF a b P L).eval x = WideDefect.output (a.eval x) (b.eval x)
      (fun i => (P i).eval x) (fun i => (L i).eval x) := by
  simp [outputF, Formula.conj, Formula.disj, Formula.eval, Kind.apply, eval_dirty, eval_diagonal, WideDefect.output]

theorem dirty_node {n m} (a b : Formula n) (P L : Fin (m+1) → Formula n) :
    (Kind.conj, dirtyF a b P L) ∈ (outputF a b P L).nodes := by
  simp [outputF, dirtyF, Formula.conj, Formula.disj, Formula.nodes]

def point (m : ℕ) (i : Fin (m+2)) : Formula ((m+2)+(m+2)) := .var (Fin.castAdd (m+2) i)
def line (m : ℕ) (i : Fin (m+2)) : Formula ((m+2)+(m+2)) := .var (Fin.natAdd (m+2) i)

def full (m : ℕ) :=
  outputF (point m 0) (line m 0) (fun i : Fin (m+1) => point m i.succ) (fun i => line m i.succ)

def net (m : ℕ) : Circuit := circuit (full m)
def pt {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) := x (Fin.castAdd (m+2) i)
def ln {m} (x : Fin ((m+2)+(m+2)) → Bool) (i : Fin (m+2)) := x (Fin.natAdd (m+2) i)

theorem net_monotone (m) : Monotone2 (net m) := circuit_mono _
theorem net_reads (m) : ReadsBack ((m+2)+(m+2)) (net m) := circuit_reads _

theorem net_output (m) (x : Fin ((m+2)+(m+2)) → Bool) :
    (net m).eval (List.ofFn x) = WideDefect.output (pt x 0) (ln x 0)
      (fun i => pt x i.succ) (fun i => ln x i.succ) := by
  rw [net,circuit_eval]
  exact eval_output _ _ _ _ _

theorem net_dirty (m) :
    ∃ j < (net m).gates.length, (gateAt (net m) j).op = .and ∧
      ∀ x : Fin ((m+2)+(m+2)) → Bool,
        ((net m).wires (List.ofFn x)).getD ((m+2)+(m+2)+j) false =
          WideDefect.dirty (pt x 0) (ln x 0) (fun i => pt x i.succ) (fun i => ln x i.succ) := by
  let P := fun i : Fin (m+1) => point m i.succ
  let L := fun i : Fin (m+1) => line m i.succ
  obtain ⟨j,hj,hk,he⟩ := circuit_has_gate (full m) _ _ (dirty_node (point m 0) (line m 0) P L)
  exact ⟨j,hj,hk,fun x => (he x).trans (eval_dirty _ _ _ _ _)⟩

theorem witness_weight (m : ℕ) :
    ∃ j < (net m).gates.length, (gateAt (net m) j).op = .and ∧
      ∀ x : Fin ((m+2)+(m+2)) → Bool, (net m).eval (List.ofFn x) = false →
        ((net m).wires (List.ofFn x)).getD ((m+2)+(m+2)+j) false = true →
        WideDefect.weight (pt x 0) (ln x 0) (fun i => pt x i.succ) (fun i => ln x i.succ) = m+2 := by
  obtain ⟨j,hj,hk,he⟩ := net_dirty m
  refine ⟨j,hj,hk,fun x no yes => ?_⟩
  rw [net_output] at no
  rw [he] at yes
  exact WideDefect.defect_weight _ _ _ _ no yes

theorem matching_iff (m) (x : Fin ((m+2)+(m+2)) → Bool) :
    (net m).eval (List.ofFn x) = true ↔ ∃ i : Fin (m+2), pt x i = true ∧ ln x i = true := by
  rw [net_output, WideDefect.output_exact]
  simp only [Bool.or_eq_true, Bool.and_eq_true, WideDefect.diagonal, List.any_eq_true, List.mem_ofFn, id]
  constructor
  · rintro (h | ⟨v, ⟨i,rfl⟩, h⟩)
    · exact ⟨0,h⟩
    · exact ⟨i.succ,Bool.and_eq_true_iff.mp h⟩
  · rintro ⟨i,h⟩
    cases i using Fin.cases with
    | zero => exact Or.inl h
    | succ j => exact Or.inr ⟨_,⟨j,rfl⟩,Bool.and_eq_true_iff.mpr h⟩

def badInput (m : ℕ) : Fin ((m+2)+(m+2)) → Bool :=
  Fin.addCases (fun i : Fin (m+2) => decide (i = 0)) (fun i : Fin (m+2) => decide (i ≠ 0))

theorem actual_obstruction (m : ℕ) :
    ∃ j < (net m).gates.length, (gateAt (net m) j).op = .and ∧
      (net m).eval (List.ofFn (badInput m)) = false ∧
      ((net m).wires (List.ofFn (badInput m))).getD ((m+2)+(m+2)+j) false = true := by
  obtain ⟨j,hj,hk,he⟩ := net_dirty m
  refine ⟨j,hj,hk,?_⟩
  rw [net_output, he, WideDefect.unique_obstruction]
  simp only [pt,ln,badInput,Fin.addCases_left,Fin.addCases_right]
  simp

end WideNet
