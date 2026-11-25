import PEqualNP.Outside.L_meta_4795

/-!
Adjoining a fresh AND or OR input to the output increases the unrestricted
minimum by one for any nonconstant Boolean function. A monotone witness at
the old minimum extends to a monotone witness at the new minimum.
Input relabeling and one-gate elimination are from Nico Habets's L-meta-4795,
which credits sanchan's L-meta-927.
-/
namespace FreshOutput
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux
  (BFn relabel relGate rel_fold rel_init wiresFrom wiresFrom_append length_wiresFrom
    getD_snoc_eq getD_wiresFrom gate_elim_one)

inductive Kind | meet | join

def Kind.op : Kind → GateOp | .meet => .and | .join => .or
def Kind.unit : Kind → Bool | .meet => true | .join => false
def Kind.apply : Kind → Bool → Bool → Bool
  | .meet, x, z => x && z
  | .join, x, z => x || z

def adjoin {n : ℕ} (k : Kind) (f : BFn n) : BFn (n+1) := fun x =>
  k.apply (f (fun i => x i.castSucc)) (x (Fin.last n))

def Nonconstant {n : ℕ} (f : BFn n) : Prop := ∃ u v, f u ≠ f v

def Budget {n : ℕ} (ops : Set GateOp) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, (∀ g ∈ C.gates, g.op ∈ ops ∧ g.inputs.length ≤ 2) ∧
    C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

abbrev Mono {n : ℕ} (f : BFn n) (s : ℕ) : Prop := Budget {GateOp.and,GateOp.or} f s

theorem pin {n} (k : Kind) (f : BFn n) (y : Fin n → Bool) (b : Bool) :
    adjoin k f (Fin.snoc y b) = k.apply (f y) b := by simp [adjoin]

theorem pinUnit {n} (k : Kind) (f : BFn n) (y : Fin n → Bool) :
    adjoin k f (Fin.snoc y k.unit) = f y := by cases k <;> simp [pin,Kind.apply,Kind.unit]

/-- Every basis containing the chosen gate admits a one-gate extension.
An out-of-range output in the original circuit keeps the usual default-false
semantics when it is used as the operand of the appended gate. -/
theorem extend {n s} (k : Kind) (f : BFn n) (ops : Set GateOp) (hk : k.op ∈ ops)
    (hc : Budget ops f s) : Budget ops (adjoin k f) (s+1) := by
  obtain ⟨C, legal, size, ev⟩ := hc
  let D := relabel n (n+1) Fin.castSucc C
  let g : Gate := ⟨k.op,[D.output,n]⟩
  refine ⟨⟨D.gates ++ [g], n+1+D.gates.length⟩,?_,?_,?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact ⟨(legal b hb).1, by simpa [relGate] using (legal b hb).2⟩
    · have eq : a = g := by simpa using ha
      subst a
      exact ⟨hk,by simp [g]⟩
  · simpa [D,relabel,Circuit.size] using Nat.succ_le_succ size
  · intro x
    let w := wiresFrom D.gates (List.ofFn x)
    have len : w.length = n+1+D.gates.length := by simp [w,length_wiresFrom]
    have hv : w.getD D.output false = f (fun i => x i.castSucc) := by
      exact ((rel_fold n (n+1) Fin.castSucc C.gates _ _ (rel_init n (n+1) Fin.castSucc x)).2.2 C.output).trans (ev _)
    have hget : w.getD n false = x (Fin.last n) := by
      rw [show w.getD n false = (List.ofFn x).getD n false from
        getD_wiresFrom _ _ _ (by simp)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [Nat.lt_succ_self, ↓reduceDIte, Option.getD_some]
      rfl
    change (wiresFrom (D.gates ++ [g]) (List.ofFn x)).getD _ false = _
    rw [wiresFrom_append,←len]
    change (w ++ [k.op.eval [w.getD D.output false, w.getD n false]]).getD w.length false = _
    rw [getD_snoc_eq,hv,hget]
    cases k <;> simp [Kind.op, Kind.apply, adjoin, GateOp.eval]

theorem budget_iff {n s} (k : Kind) (f : BFn n) (hnc : Nonconstant f) :
    HasCircuitSize (n+1) (adjoin k f) s ↔ ∃ t, t+1 ≤ s ∧ HasCircuitSize n f t := by
  constructor
  · intro h
    obtain ⟨u,v,huv⟩ := hnc
    have val : ∃ y, f y = k.unit := by
      cases k <;> cases a : f u <;> cases b : f v <;> simp_all [Kind.unit]
      all_goals first | exact ⟨u,a⟩ | exact ⟨v,b⟩
    obtain ⟨y,hy⟩ := val
    have dep : ∃ x, adjoin k f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ adjoin k f x := by
      refine ⟨Fin.snoc y k.unit,?_⟩
      rw [Fin.snoc_last,Fin.update_snoc_last,pin,pinUnit,hy]
      cases k <;> decide
    obtain ⟨t,ht,hf⟩ := gate_elim_one n (adjoin k f) k.unit s dep
      ⟨u,v,by simpa only [pinUnit] using huv⟩ h
    exact ⟨t,ht,by simpa only [pinUnit] using hf⟩
  · rintro ⟨t,ht,hf⟩
    obtain ⟨C,hC,hz,he⟩ := extend k f {GateOp.and,GateOp.or,GateOp.not}
      (by cases k <;> simp [Kind.op]) hf
    exact ⟨C,hC,hz.trans ht,he⟩

theorem exactMinimum {n m} (k : Kind) (f : BFn n) (h : Nonconstant f)
    (attained : HasCircuitSize n f m) (least : ∀ s, HasCircuitSize n f s → m ≤ s) :
    HasCircuitSize (n+1) (adjoin k f) (m+1) ∧
    ∀ s, HasCircuitSize (n+1) (adjoin k f) s → m+1 ≤ s := by
  refine ⟨(budget_iff k f h).mpr ⟨m,le_rfl,attained⟩,?_⟩
  intro s hs
  obtain ⟨t,ht,hf⟩ := (budget_iff k f h).mp hs
  exact (Nat.succ_le_succ (least t hf)).trans ht

theorem monotoneTransfer {n} (k : Kind) (f : BFn n) (h : Nonconstant f)
    (core : ∀ t, HasCircuitSize n f t → Mono f t) :
    ∀ s, HasCircuitSize (n+1) (adjoin k f) s → Mono (adjoin k f) s := by
  intro s hs
  obtain ⟨t,ht,hf⟩ := (budget_iff k f h).mp hs
  obtain ⟨C,hC,hz,he⟩ := extend k f {GateOp.and,GateOp.or} (by cases k <;> simp [Kind.op]) (core t hf)
  exact ⟨C,hC,hz.trans ht,he⟩

namespace Row15094
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (2826995840 * 2^32 + 2290089984) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)
def core (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xe8a8a800 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)
def rotate : Fin 6 → Fin 6 := ![1,2,3,4,5,0]

set_option maxRecDepth 8192 in
theorem factor : ∀ x, target x = adjoin .meet core (x ∘ rotate) := by decide +kernel

theorem coreNonconstant : Nonconstant core :=
  ⟨fun _ => false,fun _ => true,by decide +kernel⟩

/-- Every budget on the literal six-input row reduces to a core budget exactly
one gate smaller, allowing any amount of unused budget. -/
theorem rowBudget (s : ℕ) :
    HasCircuitSize 6 target s ↔ ∃ t, t+1 ≤ s ∧ HasCircuitSize 5 core t := by
  let inverse : Fin 6 → Fin 6 := ![5,0,1,2,3,4]
  have inverseFactor : (fun x => target (x ∘ inverse)) = adjoin .meet core := by
    apply funext
    decide +kernel
  rw [← budget_iff .meet core coreNonconstant]
  constructor
  · intro h
    have ht := PEqualNP.Outside.L_meta_4795_aux.relabel_size inverse target s h
    rwa [inverseFactor] at ht
  · intro h
    have ht := PEqualNP.Outside.L_meta_4795_aux.relabel_size rotate (adjoin .meet core) s h
    rwa [← funext factor] at ht
end Row15094
end FreshOutput

#print axioms FreshOutput.exactMinimum
#print axioms FreshOutput.monotoneTransfer
#print axioms FreshOutput.Row15094.factor
#print axioms FreshOutput.Row15094.rowBudget
