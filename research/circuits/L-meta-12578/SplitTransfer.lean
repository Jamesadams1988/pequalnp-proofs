import PEqualNP.MetaComplexity.Helpers.PermInputs

/-! Replacing any essential input p by the conjunction of p and a fresh last input
raises the unrestricted minimum by exactly one and preserves monotone replacement
at every budget. The lower bound does not require the function to be monotone. -/
namespace SplitTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def split {n} (p : Fin n) (f : BFn n) : BFn (n+1) := fun x =>
  f (Function.update (fun i => x i.castSucc) p (x p.castSucc && x (Fin.last n)))

def Essential {n} (p : Fin n) (f : BFn n) : Prop :=
  ∃ y : Fin n → Bool, f (Function.update y p true) ≠ f (Function.update y p false)

def InBasis (ops : Set GateOp) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op ∈ ops ∧ g.inputs.length ≤ 2

def Budget {n} (ops : Set GateOp) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, InBasis ops C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

abbrev Mono {n} (f : BFn n) (s : ℕ) := Budget {GateOp.and,GateOp.or} f s

theorem pin {n} (p : Fin n) (f : BFn n) (y : Fin n → Bool) (b : Bool) :
    split p f (Fin.snoc y b) = f (Function.update y p (y p && b)) := by
  simp [split, Fin.snoc_castSucc, Fin.snoc_last]

theorem pin_true {n} (p : Fin n) (f : BFn n) (y : Fin n → Bool) :
    split p f (Fin.snoc y true) = f y := by
  simp [pin, Function.update_eq_self]

/-- The upper bound works for every fan-in-two gate basis that contains AND. -/
theorem extend {n s} (p : Fin n) (f : BFn n) (ops : Set GateOp) (hand : GateOp.and ∈ ops)
    (h : Budget ops f s) : Budget ops (split p f) (s+1) := by
  obtain ⟨C, legal, size, ev⟩ := h
  let π : Fin n → Fin ((n+1)+1) := fun i => if i = p then Fin.last (n+1) else i.castSucc.castSucc
  let g : Gate := ⟨.and,[p.castSucc.val,(Fin.last n).val]⟩
  let gs := C.gates.map (relGate n ((n+1)+1) π)
  let o := wmap n ((n+1)+1) π C.output
  refine ⟨⟨g::gs,o⟩, ?_, ?_, ?_⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hand, by simp [g]⟩
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
      exact ⟨(legal k hk).1, by simpa [relGate] using (legal k hk).2⟩
  · simpa [Circuit.size,gs] using Nat.succ_le_succ size
  · intro x
    let y : Fin ((n+1)+1) → Bool := Fin.snoc x (x p.castSucc && x (Fin.last n))
    have start : step (List.ofFn x) g = List.ofFn y := by
      change step (List.ofFn x) g = List.ofFn (Fin.snoc x (x p.castSucc && x (Fin.last n)))
      rw [ofFn_snoc]
      have get (i : Fin (n+1)) : (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [i.isLt, ↓reduceDIte, Option.getD_some]
      simp only [step,g,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
        id_eq,Bool.and_true,get]
    have repl : y ∘ π = Function.update (fun i : Fin n => x i.castSucc) p (x p.castSucc && x (Fin.last n)) := by
      funext i
      by_cases same : i = p
      · subst i; simp [y,π]
      · simp [y,π,same,Function.update_of_ne]
    change (gs.foldl step (step (List.ofFn x) g)).getD o false = _
    rw [start,split,←repl,←ev]
    exact (rel_fold n ((n+1)+1) π C.gates _ _ (rel_init n ((n+1)+1) π y)).2.2 C.output

theorem both_essential {n} (p : Fin n) (f : BFn n) (he : Essential p f) :
    ∀ i ∈ ({p.castSucc, Fin.last n} : Finset (Fin (n+1))),
    ∃ x, split p f (Function.update x i (!x i)) ≠ split p f x := by
  obtain ⟨y,diff⟩ := he
  let z := Function.update y p true
  intro i hi
  have cases : i = p.castSucc ∨ i = Fin.last n := by simpa using hi
  rcases cases with rfl | rfl
  · refine ⟨Fin.snoc z true, ?_⟩
    have old : Function.update (Fin.snoc z true : Fin (n+1) → Bool) p.castSucc false =
        Fin.snoc (Function.update y p false) true := by
      funext k
      refine Fin.lastCases ?_ (fun a => ?_) k
      · simp [Function.update_of_ne, Ne.symm (Fin.castSucc_ne_last p)]
      · by_cases e : a = p
        · subst a; simp
        · simp [z,e,Function.update_of_ne]
    simp only [Fin.snoc_castSucc, z, Function.update_self, Bool.not_true] at *
    rw [old, pin_true,pin_true]
    exact diff.symm
  · refine ⟨Fin.snoc z true, ?_⟩
    rw [Fin.snoc_last, Fin.update_snoc_last, pin, pin_true]
    simpa [z, Function.update_idem] using diff.symm

/-- Unrestricted budgets translate by exactly one, including the zero-budget case. -/
theorem budget_iff {n} (p : Fin n) (f : BFn n) (he : Essential p f) (s : ℕ) :
    HasCircuitSize (n+1) (split p f) s ↔ ∃ t, t+1 ≤ s ∧ HasCircuitSize n f t := by
  constructor
  · intro h
    have deps := both_essential p f he
    cases s with
    | zero =>
      have hsize := dep_lower_set _ _ _ deps 0 h
      simp [Fin.castSucc_ne_last] at hsize
    | succ t =>
      have dep := deps (Fin.last n) (by simp)
      obtain ⟨y,hy⟩ := he
      have nc : ∃ u v, split p f (Fin.snoc u true) ≠ split p f (Fin.snoc v true) :=
        ⟨Function.update y p true, Function.update y p false, by simpa only [pin_true] using hy⟩
      have lower := gate_elim n (split p f) true t dep nc h
      exact ⟨t,le_rfl, by simpa only [pin_true] using lower⟩
  · rintro ⟨t,ts,h⟩
    obtain ⟨C,ok,size,ev⟩ := extend p f {GateOp.and,GateOp.or,GateOp.not} (by simp) h
    exact ⟨C,ok,size.trans ts,ev⟩

theorem successor_budget {n} (p : Fin n) (f : BFn n) (he : Essential p f) (s : ℕ) :
    HasCircuitSize (n+1) (split p f) (s+1) ↔ HasCircuitSize n f s := by
  rw [budget_iff p f he]
  constructor
  · rintro ⟨t,ts,C,ok,sz,ev⟩
    exact ⟨C,ok,sz.trans (by omega),ev⟩
  · exact fun h => ⟨s,le_rfl,h⟩

theorem minimum_shift {n} (p : Fin n) (f : BFn n) (he : Essential p f) (s : ℕ)
    (attained : HasCircuitSize n f s) (least : ∀ t, HasCircuitSize n f t → s ≤ t) :
    HasCircuitSize (n+1) (split p f) (s+1) ∧
      ∀ t, HasCircuitSize (n+1) (split p f) t → s+1 ≤ t := by
  refine ⟨(successor_budget p f he s).mpr attained, ?_⟩
  intro t h
  obtain ⟨u,ut,hu⟩ := (budget_iff p f he t).mp h
  exact (Nat.succ_le_succ (least u hu)).trans ut

theorem all_budget_transfer {n} (p : Fin n) (f : BFn n) (he : Essential p f)
    (core : ∀ t, HasCircuitSize n f t → Mono f t) :
    ∀ s, HasCircuitSize (n+1) (split p f) s → Mono (split p f) s := by
  intro s h
  obtain ⟨t,ts,hc⟩ := (budget_iff p f he s).mp h
  obtain ⟨C,ok,size,ev⟩ := extend p f {GateOp.and,GateOp.or} (by simp) (core t hc)
  exact ⟨C,ok,size.trans ts,ev⟩

end SplitTransfer
