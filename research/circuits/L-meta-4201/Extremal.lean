import PEqualNP.Defs

/-! A maximal false assignment of least support in the cyclic order-four
incidence graph of L-meta-4201. Point wires precede line wires. -/
namespace PG4Extremal

abbrev Vertex := Fin 42
abbrev Index := Fin 21

def Difference (p l : ℕ) : Prop := (l+21-p)%21 ∈ [0,5,7,17,20]
instance (p l : ℕ) : Decidable (Difference p l) := by unfold Difference; infer_instance

def Incidence (x : Vertex → Bool) : Prop :=
  ∃ p l : Vertex, (p.val < 21 ∧ 21 ≤ l.val ∧ Difference p.val l.val) ∧ x p = true ∧ x l = true

instance (x : Vertex → Bool) : Decidable (Incidence x) := by unfold Incidence; infer_instance

def witness (i : Vertex) : Bool := decide (i.val ∈ [0,1,4,14,23,33,36,37])
def zeros : Finset Vertex := Finset.univ.filter fun i => witness i = false

theorem witness_false : ¬ Incidence witness := by decide +kernel
theorem zeros_card : zeros.card = 34 := by decide +kernel
theorem all_flips : ∀ v ∈ zeros, Incidence (Function.update witness v true) := by decide +kernel

/-- All maximal false assignments in this graph have at least eight selected
vertices. The two maximality hypotheses say why each omitted vertex cannot
be adjoined while keeping the input false. -/
def nbr (p : Index) : Finset Index := Finset.univ.filter fun j => Difference p.val (21+j.val)
def revNbr (j : Index) : Finset Index := Finset.univ.filter fun p => Difference p.val (21+j.val)

private theorem nbrCards : (∀ p, (nbr p).card = 5) ∧ (∀ j, (revNbr j).card = 5) := by decide +kernel

private theorem covered_card (s t : Finset Index) (N : Index → Finset Index)
    (deg : ∀ i, (N i).card = 5)
    (covers : ∀ j : Index, j ∉ t → ∃ i ∈ s, j ∈ N i) :
    21 ≤ t.card + 5*s.card := by
  classical
  have span : Finset.univ ⊆ t ∪ s.biUnion N := by
    intro j _
    by_cases h : j ∈ t
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr (covers j h))
  have h := (Finset.card_le_card span).trans (Finset.card_union_le _ _)
  have hh := Finset.card_biUnion_le (s := s) (t := N)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp [deg, mul_comm] at hh
  omega

theorem maximal_support_at_least_eight (points lines : Finset Index)
    (blocksLines : ∀ j, j ∉ lines → ∃ p ∈ points, j ∈ nbr p)
    (blocksPoints : ∀ p, p ∉ points → ∃ j ∈ lines, p ∈ revNbr j) :
    8 ≤ points.card + lines.card := by
  have hp := covered_card points lines nbr nbrCards.1 blocksLines
  have hl := covered_card lines points revNbr nbrCards.2 blocksPoints
  omega

end PG4Extremal
#print axioms PG4Extremal.all_flips
#print axioms PG4Extremal.maximal_support_at_least_eight
