import PEqualNP.Defs

/-! A restricted model of flat, unshared bipartite edge formulas for L-meta-9791.
Each block separately builds its left and right OR trees and ANDs their outputs.
A final binary OR tree joins the blocks. Repeated edges and blocks are permitted. -/

namespace PEqualNP.Outside.L_meta_9791_flat

abbrev Edge := ℕ × ℕ

def graph : Finset Edge := ([(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)] : List Edge).toFinset

def matching : Finset Edge := ([(2, 13), (3, 14), (0, 15), (1, 16), (6, 17), (7, 18),
  (4, 19), (5, 20), (10, 21), (11, 22), (8, 23)] : List Edge).toFinset

theorem graph_card : graph.card = 44 := by decide +kernel

theorem matching_card : matching.card = 11 := by decide +kernel

theorem matching_inside : matching ⊆ graph := by decide +kernel

theorem disjoint_endpoints :
    ∀ a ∈ matching, ∀ b ∈ matching, a.1 = b.1 ∨ a.2 = b.2 → a = b := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem no_rectangle :
    ∀ a ∈ graph, ∀ b ∈ graph, a.1 ≠ b.1 → a.2 ≠ b.2 →
      (a.1, b.2) ∉ graph ∨ (b.1, a.2) ∉ graph := by
  decide +kernel

structure Block where
  left : Finset ℕ
  right : Finset ℕ

def Block.edges (b : Block) : Finset Edge := b.left ×ˢ b.right

def Block.Valid (b : Block) : Prop :=
  b.left.Nonempty ∧ b.right.Nonempty ∧ b.edges ⊆ graph

theorem block_is_star {b : Block} (h : b.Valid) :
    b.left.card = 1 ∨ b.right.card = 1 := by
  obtain ⟨hl, hr, hrect⟩ := h
  have lpos := Finset.card_pos.mpr hl
  have rpos := Finset.card_pos.mpr hr
  by_contra! hn
  obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp (show 1 < b.left.card by omega)
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (show 1 < b.right.card by omega)
  have edge {i j : ℕ} (hi : i ∈ b.left) (hj : j ∈ b.right) : (i, j) ∈ graph :=
    hrect (Finset.mem_product.mpr ⟨hi, hj⟩)
  rcases no_rectangle (u,x) (edge hu hx) (v,y) (edge hv hy) huv hxy with bad | bad
  · exact bad (edge hu hy)
  · exact bad (edge hv hx)

theorem matched_per_block {b : Block} (h : b.Valid) :
    (matching ∩ b.edges).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  obtain ⟨ham, hae⟩ := Finset.mem_inter.mp ha
  obtain ⟨hcm, hce⟩ := Finset.mem_inter.mp hc
  apply disjoint_endpoints a ham c hcm
  obtain ⟨hal, har⟩ := Finset.mem_product.mp hae
  obtain ⟨hcl, hcr⟩ := Finset.mem_product.mp hce
  rcases block_is_star h with hl | hr
  · exact Or.inl ((Finset.card_le_one.mp hl.le) _ hal _ hcl)
  · exact Or.inr ((Finset.card_le_one.mp hr.le) _ har _ hcr)

/-- Separate binary OR trees for each side, then one AND gate. -/
def Block.gates (b : Block) := (b.left.card - 1) + (b.right.card - 1) + 1

theorem edge_cost {b : Block} (h : b.Valid) : b.gates = b.edges.card := by
  have hl := Finset.card_pos.mpr h.1
  have hr := Finset.card_pos.mpr h.2.1
  simp only [Block.gates, Block.edges, Finset.card_product]
  rcases block_is_star h with q | q <;> simp [q] <;> omega

/-- The cost adds each block independently and charges the final binary OR tree. -/
def flatGates {ι : Type*} (s : Finset ι) (B : ι → Block) : ℕ :=
  (∑ i ∈ s, (B i).gates) + (s.card - 1)

theorem eleven_blocks {ι : Type*} (s : Finset ι) (B : ι → Block)
    (valid : ∀ i ∈ s, (B i).Valid) (cover : graph ⊆ s.biUnion (fun i => (B i).edges)) :
    11 ≤ s.card := by
  have inc : matching ⊆ s.biUnion (fun i => matching ∩ (B i).edges) := by
    intro e he
    obtain ⟨i, hi, him⟩ := Finset.mem_biUnion.mp (cover (matching_inside he))
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨he, him⟩⟩
  calc
    11 = matching.card := matching_card.symm
    _ ≤ _ := Finset.card_le_card inc
    _ ≤ ∑ i ∈ s, (matching ∩ (B i).edges).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum (fun i hi => matched_per_block (valid i hi))
    _ = _ := by simp

/-- Every flat unshared cover by positive bipartite blocks needs at least 54 gates. -/
theorem flat_lower_bound {ι : Type*} (s : Finset ι) (B : ι → Block)
    (valid : ∀ i ∈ s, (B i).Valid) (cover : graph ⊆ s.biUnion (fun i => (B i).edges)) :
    54 ≤ flatGates s B := by
  have hblocks := eleven_blocks s B valid cover
  have hcost : 44 ≤ ∑ i ∈ s, (B i).gates := calc
    44 = graph.card := graph_card.symm
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ i ∈ s, (B i).edges.card := Finset.card_biUnion_le
    _ = _ := Finset.sum_congr rfl (fun i hi => (edge_cost (valid i hi)).symm)
  unfold flatGates
  omega

/-- The 11 right-hand stars attain the lower bound. -/
def columns : Finset ℕ := {13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}

def column (v : ℕ) : Block := ⟨(graph.filter (fun e => e.2 = v)).image Prod.fst, {v}⟩

set_option maxHeartbeats 3000000 in
theorem columns_attain :
    (∀ v ∈ columns, (column v).Valid) ∧
      graph ⊆ columns.biUnion (fun v => (column v).edges) ∧ flatGates columns column = 54 := by
  unfold Block.Valid
  decide +kernel

end PEqualNP.Outside.L_meta_9791_flat
