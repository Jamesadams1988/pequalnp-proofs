import FreshOutput

/-! The head of the list gives the outermost gate. Each gate takes the previous
output and a distinct new primary input. Neutral values preserve the inner
function, so every intermediate output remains nonconstant. -/
namespace FreshOutput
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4795_aux (BFn)

def chain {n : ℕ} (f : BFn n) : (ks : List Kind) → BFn (n + ks.length)
  | [] => f
  | k :: ks => adjoin k (chain f ks)

theorem chainNonconstant {n} (f : BFn n) (h : Nonconstant f) (ks : List Kind) :
    Nonconstant (chain f ks) := by
  induction ks with
  | nil => exact h
  | cons k ks ih =>
    obtain ⟨u,v,hne⟩ := ih
    exact ⟨Fin.snoc u k.unit, Fin.snoc v k.unit, by simpa only [chain,pinUnit] using hne⟩

theorem chainExact {n m} (f : BFn n) (h : Nonconstant f) (ks : List Kind)
    (attained : HasCircuitSize n f m) (least : ∀ s, HasCircuitSize n f s → m ≤ s) :
    HasCircuitSize (n+ks.length) (chain f ks) (m+ks.length) ∧
    ∀ s, HasCircuitSize (n+ks.length) (chain f ks) s → m+ks.length ≤ s := by
  induction ks with
  | nil => exact ⟨attained,least⟩
  | cons k ks ih => exact exactMinimum k (chain f ks) (chainNonconstant f h ks) ih.1 ih.2

theorem chainMono {n m} (f : BFn n) (ks : List Kind) (witness : Mono f m) :
    Mono (chain f ks) (m+ks.length) := by
  induction ks with
  | nil => exact witness
  | cons k ks ih =>
    exact extend k (chain f ks) {GateOp.and,GateOp.or} (by cases k <;> simp [Kind.op]) ih

end FreshOutput
#print axioms FreshOutput.chainExact
#print axioms FreshOutput.chainMono
