import PEqualNP.Defs

/-! Count the distinct gates whose readiness switches along an increasing chain. -/
namespace Row4201.Charging
open PEqualNP.CircuitLowerBounds

def isOr (g : Gate) : Bool := GateOp.casesOn g.op false true false (fun _ => false) false

private theorem occCount (gs : List Gate) :
    (Finset.univ.filter (fun j : Fin gs.length => isOr gs[j] = true)).card =
      gs.countP isOr := by
  let inds := List.finRange gs.length
  have hu : inds.toFinset = Finset.univ := by ext i; simp [inds]
  rw [← hu, (List.nodup_finRange gs.length).card_eq_countP]
  have h := List.countP_map (p := isOr)
    (f := fun i : Fin gs.length => gs[i]) (l := inds)
  simpa [inds, List.map_getElem_finRange, Function.comp_def, beq_iff_eq] using h.symm

theorem countWithCore {K : ℕ} (gs : List Gate) (ready : Fin gs.length → ℕ → Prop)
    (core : Finset (Fin gs.length))
    (coreState : ∀ j ∈ core, isOr gs[j] = true ∧ ready j 0)
    (persist : ∀ j {a b}, a ≤ b → ready j a → ready j b)
    (hit : ∀ k : Fin K, ∃ j : Fin gs.length, isOr gs[j] = true ∧
      ¬ ready j k.val ∧ ready j (k.val+1)) :
    K + core.card ≤ gs.countP isOr := by
  classical
  choose index hop hoff hon using hit
  have distinct {i j : Fin K} (before : i.val < j.val) : index i ≠ index j := by
    intro eq
    exact hoff j (eq ▸ persist (index i) (show i.val+1 ≤ j.val by omega) (hon i))
  have inject : Function.Injective index := by
    intro i j eq
    rcases lt_trichotomy i.val j.val with lt | same | gt
    · exact (distinct lt eq).elim
    · exact Fin.ext same
    · exact (distinct gt eq.symm).elim
  let ors := Finset.univ.filter (fun j : Fin gs.length => isOr gs[j] = true)
  have outside (k : Fin K) : index k ∉ core := by
    intro member
    exact hoff k (persist _ (Nat.zero_le _) (coreState _ member).2)
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin K)))
    (t := ors \ core) index
    (fun k _ => Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop k⟩, outside k⟩)
    (fun _ _ _ _ eq => inject eq)
  have sub : core ⊆ ors := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (coreState j hj).1⟩
  have add := Finset.card_sdiff_add_card_eq_card sub
  have full : ors.card = gs.countP isOr := occCount gs
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

end Row4201.Charging
#print axioms Row4201.Charging.countWithCore
