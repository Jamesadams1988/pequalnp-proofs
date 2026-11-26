import Elimination
import PEqualNP.Outside.L_meta_614

namespace Plane9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Elimination (V edgePairs)

def directed (u v : V) : Prop :=
  u.val < 13 ∧ 13 ≤ v.val ∧ ((v.val + 13 - u.val) % 13 ∈ [0,4,10,12]) ∧ (u.val,v.val) ≠ (0,13)
instance (u v : V) : Decidable (directed u v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def G := SimpleGraph.fromRel directed
instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (directed u v ∨ directed v u)))

theorem table : ∀ u v : V, G.Adj u v ↔ (u.val,v.val) ∈ edgePairs ∨ (v.val,u.val) ∈ edgePairs := by decide +kernel

theorem two : ∀ u : V, ∃ a b : V, a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by decide +kernel

theorem degree (u : V) : 2 ≤ (G.neighborSet u).ncard := by
  obtain ⟨a,b,h,ha,hb⟩ := two u
  rw [← Set.ncard_pair h]
  exact Set.ncard_le_ncard (show ({a,b} : Set V) ⊆ G.neighborSet u from by
    intro z hz
    rcases hz with e | e
    · exact e ▸ ha
    · change z = b at e
      exact e ▸ hb)

def left (p : Fin 13) : V := Fin.castAdd 13 p
def right (p : Fin 13) : V := Fin.natAdd 13 (p+4)
theorem matched : ∀ p : Fin 13, G.Adj (left p) (right p) := by decide +kernel
theorem distinctPairs : ∀ p q : Fin 13,
    (left p = left q ∨ left p = right q ∨ right p = left q ∨ right p = right q) → p=q := by decide +kernel

theorem cover_bound (S : Finset V) (h : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) :
    13 ≤ S.card := by
  let pick (p : Fin 13) : V := if left p ∈ S then left p else right p
  have mem (p) : pick p ∈ S := by
    dsimp [pick]
    split <;> grind [matched]
  have inj : Function.Injective pick := by
    intro p q eq
    apply distinctPairs
    dsimp [pick] at eq
    split at eq <;> split at eq <;> tauto
  have bound := Finset.card_le_card (show Finset.univ.image pick ⊆ S by
    intro i hi
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hi
    exact mem p)
  simpa [Finset.card_image_of_injective _ inj] using bound

theorem monotone_lower (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : V, (u.val,v.val) ∈ edgePairs ∧ x u = true ∧ x v = true) : 38 ≤ C.size := by
  have twins : ∀ u v : V, u ≠ v → ∃ w, ¬(G.Adj u w ↔ G.Adj v w) := by decide +kernel
  have pair : ∀ u v : V, G.Adj u v → ∃ a b, G.Adj u a ∧ a ≠ v ∧ G.Adj v b ∧ b ≠ u ∧ (a=b ∨ ¬G.Adj a b) := by decide +kernel
  let L := Finset.univ.filter fun i : V => i.val < 13
  have lr : ∀ u v : V, G.Adj u v → u ∈ L ∨ v ∈ L := by decide +kernel
  have sizeL : L.card = 13 := by decide +kernel
  have h := PEqualNP.Outside.L_meta_614 26 13 G C (fun u => by obtain ⟨a,b,_,ha,_⟩ := two u; exact ⟨a,ha⟩)
    (fun u v h _ _ _ => twins u v h) (fun u v h _ _ => pair u v h)
    ⟨L,fun u v h _ _ => lr u v h,sizeL⟩
    (fun S hS => cover_bound S (fun u v h => hS u v h (degree u) (degree v))) hm (fun x => by
      rw [hc]
      constructor
      · rintro ⟨u,v,e,hu,hv⟩
        exact ⟨u,v,(table u v).mpr (Or.inl e),hu,hv⟩
      · rintro ⟨u,v,e,hu,hv⟩
        rcases (table u v).mp e with he | he
        · exact ⟨u,v,he,hu,hv⟩
        · exact ⟨v,u,he,hv,hu⟩)
  omega

/-- The assigned proposition, with only its numerical budget weakened. -/
theorem literal_monotone : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 37 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, hc⟩
  have h := monotone_lower C hm hc
  omega
end Plane9742
#print axioms Plane9742.literal_monotone
