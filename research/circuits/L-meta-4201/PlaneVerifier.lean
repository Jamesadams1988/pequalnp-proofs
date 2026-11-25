import ExtremalVerifier

/-! The concrete 21-point, 21-line graph of L-meta-4201. A closed point set
and its common non-neighbor lines specify a maximal false input. -/
namespace PlaneVerifier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ExtremalVerifier

abbrev V := Fin 42

def edge (p l : V) : Prop := p.val < 21 ∧ 21 ≤ l.val ∧
  (l.val + 21 - p.val) % 21 ∈ [0,5,7,17,20]

instance (p l : V) : Decidable (edge p l) := by unfold edge; infer_instance

/-- All lines compatible with every point in the given set. -/
def right (a : Finset V) : Finset V :=
  Finset.univ.filter (fun l => 21 ≤ l.val ∧ ∀ p ∈ a, ¬edge p l)

/-- All points compatible with every line in the given set. -/
def left (b : Finset V) : Finset V :=
  Finset.univ.filter (fun p => p.val < 21 ∧ ∀ l ∈ b, ¬edge p l)

private theorem memR {a : Finset V} {l : V} : l ∈ right a ↔ 21 ≤ l.val ∧ ∀ p ∈ a, ¬edge p l := by
  simp [right]
private theorem memL {b : Finset V} {p : V} : p ∈ left b ↔ p.val < 21 ∧ ∀ l ∈ b, ¬edge p l := by
  simp [left]

private theorem leftExtend (a : Finset V) (ha : ∀ p ∈ a, p.val < 21) : a ⊆ left (right a) :=
  fun p hp => memL.mpr ⟨ha p hp,fun _ hl => (memR.mp hl).2 p hp⟩

theorem rightClosure (a : Finset V) (ha : ∀ p ∈ a, p.val < 21) :
    right (left (right a)) = right a := by
  ext l
  constructor
  · intro hl
    exact memR.mpr ⟨(memR.mp hl).1,fun p hp => (memR.mp hl).2 p (leftExtend a ha hp)⟩
  · intro hl
    exact memR.mpr ⟨(memR.mp hl).1,fun p hp => (memL.mp hp).2 l hl⟩

private theorem independentClosed (a : Finset V) (fixed : left (right a) = a) :
    independent edge (a ∪ right a) := by
  intro p hp l hl inc
  have pA : p ∈ a := (Finset.mem_union.mp hp).resolve_right (fun h => (Nat.not_le.mpr inc.1) (memR.mp h).1)
  have lB : l ∈ right a := (Finset.mem_union.mp hl).resolve_left (by
    intro h
    rw [←fixed] at h
    exact Nat.not_lt.mpr inc.2.1 (memL.mp h).1)
  exact (memR.mp lB).2 p pA inc

theorem maximalOfClosed (a : Finset V) (fixed : left (right a) = a) :
    maximalIndependent edge (a ∪ right a) := by
  refine ⟨independentClosed a fixed, ?_⟩
  intro t ht good
  apply Finset.Subset.antisymm _ ht
  intro v hv
  by_cases side : v.val < 21
  · apply Finset.mem_union_left
    rw [←fixed]
    exact memL.mpr ⟨side,fun l hl => good v hv l (ht (Finset.mem_union_right _ hl))⟩
  · apply Finset.mem_union_right
    exact memR.mpr ⟨by omega,fun p hp => good p (ht (Finset.mem_union_left _ hp)) v hv⟩

theorem closedOfMaximal (s : Finset V) (hs : maximalIndependent edge s) :
    ∃ a : Finset V, left (right a) = a ∧ s = a ∪ right a := by
  let a := s.filter (fun v => v.val < 21)
  have memA {v} : v ∈ a ↔ v ∈ s ∧ v.val < 21 := Finset.mem_filter
  have typed : ∀ p ∈ a, p.val < 21 := fun _ hp => (memA.mp hp).2
  have stable := rightClosure a typed
  have fix : left (right (left (right a))) = left (right a) := congrArg left stable
  refine ⟨left (right a),fix,?_⟩
  apply Eq.symm
  apply hs.2 _ _ (independentClosed _ fix)
  rw [stable]
  intro v hv
  by_cases side : v.val < 21
  · exact Finset.mem_union_left _ (leftExtend a typed (memA.mpr ⟨hv,side⟩))
  · exact Finset.mem_union_right _ (memR.mpr ⟨by omega,fun p hp => hs.1 p (memA.mp hp).1 v hv⟩)

/-- Exactly the circuit-correctness hypothesis in L-meta-4201, reduced to the
edge pairs and one false input for each Galois-closed point set. -/
theorem tests (C : Circuit) (hm : Monotone2 C) :
    (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧
        (l.val + 21 - p.val) % 21 ∈ [0,5,7,17,20]) ∧ x p = true ∧ x l = true) ↔
    (∀ p l, edge p l → run C {p,l} = true) ∧
    (∀ a, left (right a) = a → run C (a ∪ right a) = false) := by
  change (∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l, edge p l ∧ x p = true ∧ x l = true) ↔ _
  rw [edgeAndMaximalTests edge C hm]
  constructor
  · rintro ⟨on,off⟩
    exact ⟨on,fun a h => off _ (maximalOfClosed a h)⟩
  · rintro ⟨on,off⟩
    refine ⟨on,fun s hs => ?_⟩
    obtain ⟨a,fix,rfl⟩ := closedOfMaximal s hs
    exact off a fix

/-- Enumerate every closed point set once by selecting the fixed points among
the subsets of the twenty-one point inputs. -/
def closedPoints : Finset (Finset V) :=
  (Finset.univ.filter (fun p : V => p.val < 21)).powerset.filter (fun a => left (right a) = a)

theorem memClosedPoints {a : Finset V} : a ∈ closedPoints ↔ left (right a) = a := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro fixed
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,fixed⟩
    intro p hp
    rw [←fixed] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,(memL.mp hp).1⟩

def edgePairs : Finset (V × V) := Finset.univ.filter (fun z => edge z.1 z.2)

set_option maxRecDepth 30000 in
theorem countEdgePairs : edgePairs.card = 105 := by decide +kernel

/-- A finite, executable specification. Each distinct selected support
contributes exactly one output test. -/
def verify (C : Circuit) : Bool :=
  decide ((∀ z ∈ edgePairs, run C {z.1,z.2} = true) ∧
    ∀ a ∈ closedPoints, run C (a ∪ right a) = false)

theorem verifyCorrect (C : Circuit) (hm : Monotone2 C) :
    verify C = true ↔ ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l, edge p l ∧ x p = true ∧ x l = true := by
  rw [show (∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l, edge p l ∧ x p = true ∧ x l = true) ↔ _ from tests C hm]
  simp [verify, edgePairs, memClosedPoints, Prod.forall]

end PlaneVerifier

#print axioms PlaneVerifier.tests
#print axioms PlaneVerifier.countEdgePairs
#print axioms PlaneVerifier.verifyCorrect
