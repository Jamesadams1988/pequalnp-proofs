import FreshOutput

/-! Inserting a fresh output operand at any coordinate. The other input indices
keep their order. This transports the fresh-last-input bounds of FreshOutput
and preserves every gate basis under an arbitrary input relabeling. -/
namespace FreshOutputAt
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux (BFn relabel relGate rel_fold rel_init relabel_size)
open FreshOutput

/-- Relabeling input wires preserves the selected gate basis, including for
noninjective maps, and preserves the original gate count. -/
theorem budgetRelabel {n m s} (π : Fin n → Fin m) (f : BFn n) (ops : Set GateOp)
    (hc : Budget ops f s) : Budget ops (fun x => f (x ∘ π)) s := by
  obtain ⟨C,hl,hz,he⟩ := hc
  refine ⟨relabel n m π C,?_,?_,?_⟩
  · intro g hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hl b hb).1,by simpa [relGate] using (hl b hb).2⟩
  · simpa [relabel,Circuit.size] using hz
  · intro x
    exact ((rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output).trans (he _)

def atInput {n} (p : Fin (n+1)) (k : Kind) (f : BFn n) : BFn (n+1) :=
  fun x => k.apply (f (x ∘ p.succAbove)) (x p)

def move {n} (p : Fin (n+1)) : Fin (n+1) → Fin (n+1) := Fin.snoc p.succAbove p
def undo {n} (p : Fin (n+1)) : Fin (n+1) → Fin (n+1) := p.insertNth (Fin.last n) Fin.castSucc

theorem moved {n} (p : Fin (n+1)) (k : Kind) (f : BFn n) :
    (fun x => adjoin k f (x ∘ move p)) = atInput p k f := by
  funext x
  simp [adjoin,atInput,move,Function.comp_def]

theorem restored {n} (p : Fin (n+1)) (k : Kind) (f : BFn n) :
    (fun x => atInput p k f (x ∘ undo p)) = adjoin k f := by
  funext x
  simp [adjoin,atInput,undo,Function.comp_def]

theorem budget_iff {n s} (p : Fin (n+1)) (k : Kind) (f : BFn n) (hn : Nonconstant f) :
    HasCircuitSize (n+1) (atInput p k f) s ↔ ∃ t, t+1 ≤ s ∧ HasCircuitSize n f t := by
  rw [← FreshOutput.budget_iff k f hn]
  constructor
  · intro h
    have hi := relabel_size (undo p) _ _ h
    rwa [restored] at hi
  · intro h
    have hi := relabel_size (move p) _ _ h
    rwa [moved] at hi

theorem liftBasis {n s} (p : Fin (n+1)) (k : Kind) (f : BFn n) (ops : Set GateOp)
    (hk : k.op ∈ ops) (hc : Budget ops f s) : Budget ops (atInput p k f) (s+1) := by
  have ht := budgetRelabel (move p) _ _ (extend k f ops hk hc)
  rwa [moved] at ht

theorem minimum_shift {n m} (p : Fin (n+1)) (k : Kind) (f : BFn n) (hn : Nonconstant f)
    (existsCore : HasCircuitSize n f m) (minimum : ∀ s, HasCircuitSize n f s → m ≤ s) :
    HasCircuitSize (n+1) (atInput p k f) (m+1) ∧
      ∀ s, HasCircuitSize (n+1) (atInput p k f) s → m+1 ≤ s := by
  refine ⟨(budget_iff p k f hn).mpr ⟨_,le_rfl,existsCore⟩,?_⟩
  intro s h
  obtain ⟨t,ht,hc⟩ := (budget_iff p k f hn).mp h
  exact (Nat.succ_le_succ (minimum t hc)).trans ht

theorem replacement {n} (p : Fin (n+1)) (k : Kind) (f : BFn n) (hn : Nonconstant f)
    (core : ∀ t, HasCircuitSize n f t → Mono f t) :
    ∀ s, HasCircuitSize (n+1) (atInput p k f) s → Mono (atInput p k f) s := by
  intro s h
  obtain ⟨t,ht,hc⟩ := (budget_iff p k f hn).mp h
  obtain ⟨C,hl,hz,he⟩ := liftBasis p k f {GateOp.and,GateOp.or} (by cases k <;> simp [Kind.op]) (core t hc)
  exact ⟨C,hl,hz.trans ht,he⟩

end FreshOutputAt
#print axioms FreshOutputAt.minimum_shift
#print axioms FreshOutputAt.replacement
