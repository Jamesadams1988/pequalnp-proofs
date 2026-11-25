import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_8657

/-!
Gate elimination and input relabeling from nicohabets's L-meta-4795, crediting
sanchan, let us transfer a lower bound from a nonconstant face to its parent.
The map of remaining inputs may identify variables and may ignore inputs.
The concrete application below uses Noptus’s seven-gate lower bound from row 8657.
-/

namespace CofactorBound

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4795_aux (one_gate_at relabel_size)

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def Lower {n : ℕ} (f : BFn n) (k : ℕ) : Prop :=
  ∀ s, HasCircuitSize n f s → k ≤ s

/-- A nonconstant image of an essential cofactor costs at least one fewer gate. -/
theorem ofPinnedImage {n m k : ℕ} {f : BFn (n+1)} {g : BFn m}
    (p : Fin (n+1)) (b : Bool) (label : Fin (n+1) → Fin m)
    (essential : ∃ x, f (Function.update x p (!x p)) ≠ f x)
    (image : ∀ y, f (Function.update (y ∘ label) p b) = g y)
    (nonconstant : ∃ u v, g u ≠ g v)
    (lower : Lower g k) : Lower f (k+1) := by
  intro s h
  obtain ⟨u,v,huv⟩ := nonconstant
  have nc : ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b) :=
    ⟨u ∘ label, v ∘ label, by simpa only [image] using huv⟩
  obtain ⟨t,ht,hface⟩ := one_gate_at n f p b s essential nc h
  have hg := relabel_size label _ t hface
  change HasCircuitSize m (fun y => f (Function.update (y ∘ label) p b)) t at hg
  rw [funext image] at hg
  exact le_trans (Nat.succ_le_succ (lower t hg)) ht

namespace Row13646

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372970 * 2^32 + 4007717088)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

/-- The five free inputs, in the order used by the previously certified table,
are original inputs 0, 3, 1, 4 and 5. The label at coordinate 2 is overwritten. -/
def label : Fin 6 → Fin 5 := ![0,2,0,1,3,4]

set_option maxRecDepth 8192 in
theorem core_image : ∀ y, target (Function.update (y ∘ label) 2 false) =
    PEqualNP.Outside.L_meta_8657.fn 0xeaaac880 y := by
  decide +kernel

/-- Input 2 is essential on the singleton {0}. Its zero cofactor is row 8657,
whose unrestricted lower bound supplies seven gates. -/
theorem eight : Lower target 8 :=
  ofPinnedImage 2 false label
    ⟨fun i => decide (i = 0), by decide +kernel⟩ core_image
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩ PEqualNP.Outside.L_meta_8657.lower

/-- The eight-gate circuit evaluates the minimal terms by grouping 02, 12,
034 and 134 together, then ORing in 05 and 013. -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩,
    ⟨.and, [1, 3]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩

set_option maxRecDepth 8192 in
theorem witness_correct : Monotone2 witness ∧ witness.size = 8 ∧
    ∀ x, witness.eval (List.ofFn x) = target x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [witness, Monotone2]
  · decide +kernel

theorem exactMinimum : HasCircuitSize 6 target 8 ∧ Lower target 8 ∧
    Monotone2 witness ∧ witness.size = 8 ∧ ∀ x, witness.eval (List.ofFn x) = target x := by
  obtain ⟨hm,hs,he⟩ := witness_correct
  have legal : FanInTwo witness := by
    intro g hg
    obtain ⟨hop, har⟩ := hm g hg
    exact ⟨hop.elim Or.inl (fun h => Or.inr (Or.inl h)), har⟩
  exact ⟨⟨witness, legal, hs.le, he⟩, eight, hm, hs, he⟩

theorem assignedStatementFalse : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro claim
  apply claim
  intro s h
  obtain ⟨hm,hs,he⟩ := witness_correct
  exact ⟨witness, hm, by rw [hs]; exact eight s h, he⟩

end Row13646
end CofactorBound

#print axioms CofactorBound.ofPinnedImage
#print axioms CofactorBound.Row13646.exactMinimum
#print axioms CofactorBound.Row13646.assignedStatementFalse
