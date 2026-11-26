import FactorCount

namespace IncidenceReadTwo.PrivateFrontier

open Finset IncidenceReadTwo.FactorCount
variable {P L : Type*} [DecidableEq P] [DecidableEq L] [Fintype L]

/-- Every frontier wire is an OR gate or one of the two kinds of raw input. -/
def Classified (F orGates : Finset ℕ) (ap : ℕ → Finset P) (al : ℕ → Finset L) : Prop :=
  ∀ j ∈ F, j ∈ orGates ∨ (∃ p, ap j = {p} ∧ al j = ∅) ∨ (∃ l, ap j = ∅ ∧ al j = {l})

omit [DecidableEq P] [DecidableEq L] [Fintype L] in
/-- No raw input can hit every edge of two rows each having two distinct neighbors. -/
theorem all_or (F orGates : Finset ℕ) (ap : ℕ → Finset P) (al : ℕ → Finset L)
    (U : Finset P) (accepted : P → Finset L) (rows : 1 < U.card)
    (degrees : ∀ p ∈ U, 1 < (accepted p).card)
    (accept : ∀ p ∈ U, ∀ l ∈ accepted p, ∀ j ∈ F, p ∈ ap j ∨ l ∈ al j)
    (classified : Classified F orGates ap al) : F ⊆ orGates := by
  intro j hj
  rcases classified j hj with gate | ⟨p,hp,hl⟩ | ⟨l,hp,hl⟩
  · exact gate
  · obtain ⟨p', hp', ne⟩ := exists_mem_ne rows p
    obtain ⟨l,hl'⟩ := card_pos.mp (by have := degrees p' hp'; omega : 0 < (accepted p').card)
    have hit := accept p' hp' l hl' j hj
    simp [hp,hl,ne] at hit
  · obtain ⟨p,hp'⟩ := card_pos.mp (by omega : 0 < U.card)
    obtain ⟨l',hl',ne⟩ := exists_mem_ne (degrees p hp') l
    have hit := accept p hp' l' hl' j hj
    simp [hp,hl,ne] at hit

/-- Frontier and conjunction wire identities in the backwards conjunction program. -/
def andWires (nodes : List Join) : Finset ℕ := (nodes.map Join.wire).toFinset

/-- Count distinct removable gates. The caller identifies the wires used elsewhere. -/
def privateWires (nodes : List Join) (root : ℕ) (external : Finset ℕ) : Finset ℕ :=
  (andWires nodes ∪ frontier nodes root) \ external

private theorem square_identity (t : ℕ) : 2 * (1 + t + t.choose 2) = t^2 + t + 2 := by
  have e : 2 * t.choose 2 = t * (t-1) := by
    rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self t)]
  cases t with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one] at e
    nlinarith

/-- Composing the factor count with counting distinct physical gate IDs. External uses
    are permitted for frontier ORs, with one unit of charge lost per such output. -/
theorem dense_private (neighbors accepted : P → Finset L) (U : Finset P)
    (nodes : List Join) (root : ℕ) (orGates external : Finset ℕ)
    (ap : ℕ → Finset P) (al : ℕ → Finset L)
    (sub : ∀ p, accepted p ⊆ neighbors p)
    (linear : ∀ p u, p ≠ u → (neighbors p ∩ neighbors u).card ≤ 1)
    (rows : 1 < U.card) (degrees : ∀ p ∈ U, 2 < (accepted p).card)
    (accept : ∀ p ∈ U, ∀ l ∈ accepted p, ∀ j ∈ frontier nodes root, p ∈ ap j ∨ l ∈ al j)
    (safe : ∀ s t, (∀ j ∈ frontier nodes root, Hit (ap j) (al j) s t) →
      ∃ p ∈ s, ∃ l ∈ t, l ∈ neighbors p)
    (classified : Classified (frontier nodes root) orGates ap al)
    (uniqueIds : (nodes.map Join.wire).Nodup)
    (gateTypes : Disjoint (andWires nodes) orGates)
    (privateAnd : Disjoint (andWires nodes) external) :
    U.card^2 + U.card + 1 ≤ (privateWires nodes root external).card +
      (frontier nodes root ∩ external).card := by
  classical
  let F := frontier nodes root
  have ors : F ⊆ orGates := all_or F orGates ap al U accepted rows
    (fun p hp => by have := degrees p hp; omega) accept classified
  have dis : Disjoint (andWires nodes) F := gateTypes.mono_right ors
  have andCount : (andWires nodes).card = nodes.length := by
    simpa only [andWires,List.length_map] using List.toFinset_card_of_nodup uniqueIds
  have inter : (andWires nodes ∪ F) ∩ external = F ∩ external := by
    rw [union_inter_distrib_right,disjoint_iff_inter_eq_empty.mp privateAnd,empty_union]
  have gateCount := card_sdiff_add_card_inter (andWires nodes ∪ F) external
  change (privateWires nodes root external).card + ((andWires nodes ∪ F) ∩ external).card = _ at gateCount
  rw [inter,card_union_of_disjoint dis,andCount] at gateCount
  have bound := factors neighbors accepted U 2 (fun j : ↥F => ap j) (fun j : ↥F => al j)
    sub linear degrees (fun p hp l hl j => accept p hp l hl j j.property)
    (fun s t h => safe s t (fun j hj => h ⟨j,hj⟩))
  rw [upToTwo,Fintype.card_coe] at bound
  have available : F.card ≤ nodes.length + 1 := frontier_card nodes root
  have twice := square_identity U.card
  change _ ≤ (privateWires nodes root external).card + (F ∩ external).card
  omega

omit [DecidableEq P] [DecidableEq L] [Fintype L] in
/-- With t ≥ m and at most two shared frontier outputs, there are enough private
    gates for all row stars. With none shared the saving is at least two. -/
theorem star_budget (U : Finset P) (accepted : P → Finset L) (m available shared : ℕ)
    (active : 0 < U.card) (width : m ≤ U.card) (maxDeg : ∀ p ∈ U, (accepted p).card ≤ m)
    (bound : U.card^2 + U.card + 1 ≤ available + shared) :
    let cost := (∑ p ∈ U, (accepted p).card) + U.card - 1
    cost + 2 ≤ available + shared ∧ (shared ≤ 2 → cost ≤ available) := by
  dsimp only
  have size : (∑ p ∈ U, (accepted p).card) ≤ U.card*m := by
    simpa using sum_le_sum maxDeg
  have cap := Nat.mul_le_mul_left U.card width
  rw [pow_two] at bound
  constructor <;> omega

end IncidenceReadTwo.PrivateFrontier

#print axioms IncidenceReadTwo.PrivateFrontier.dense_private
#print axioms IncidenceReadTwo.PrivateFrontier.star_budget
