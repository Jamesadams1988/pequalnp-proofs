import SixCycle
namespace SmallIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ForestIncidence SimpleGraph
open scoped Sym2

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Separated {N : ℕ} (I : Fin N → Fin N → Prop) := ∀ p l, I p l →
  ∃ t : Fin (N+N) → Bool, t (Fin.castAdd N p) ≠ t (Fin.natAdd N l) ∧
    ∀ a b, I a b → (a,b) ≠ (p,l) → t (Fin.castAdd N a) = t (Fin.natAdd N b)

private theorem color_walk {V : Type} {G : SimpleGraph V} (t : V → Bool)
    (h : ∀ u v, G.Adj u v → t u = t v) {u v : V} (w : G.Walk u v) : t u = t v := by
  induction w with
  | nil => rfl
  | cons a w ih => exact (h _ _ a).trans ih

private theorem is_bridge {N : ℕ} (I : Fin N → Fin N → Prop) (h : Separated I)
    {p l : Fin N} (incident : I p l) :
    (graph I).IsBridge s(Fin.castAdd N p,Fin.natAdd N l) := by
  obtain ⟨t,sep,cut⟩ := h p l incident
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨walk⟩
  apply sep
  apply color_walk t _ walk
  intro u v uv
  obtain ⟨hadj,other⟩ := SimpleGraph.deleteEdges_adj.mp uv
  obtain ⟨a,b,edge,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := hadj
  · apply cut a b edge
    rintro heq
    cases heq
    exact other (by simp)
  · symm
    apply cut a b edge
    rintro heq
    cases heq
    exact other (Set.mem_singleton_iff.mpr Sym2.eq_swap)

theorem forest_of_separated {N : ℕ} (I : Fin N → Fin N → Prop)
    (h : Separated I) : (graph I).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  rintro a b ⟨p,l,he,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
  · exact is_bridge I h he
  · rw [Sym2.eq_swap]; exact is_bridge I h he

def rectangleFree (B : Fin 3 → Fin 3 → Bool) : Prop := ∀ p p' l l',
    p ≠ p' → l ≠ l' → ¬(B p l = true ∧ B p l' = true ∧ B p' l = true ∧ B p' l' = true)

def sixCycleShape (B : Fin 3 → Fin 3 → Bool) : Prop :=
  ∃ π : Fin 3 → Fin 3, Function.Injective π ∧ ∀ p l, B p l = true ↔ π p ≠ l

def cuts (B : Fin 3 → Fin 3 → Bool) : Prop := Separated (fun p l => B p l = true)
instance (B) : Decidable (rectangleFree B) := by unfold rectangleFree; infer_instance
instance (B) : Decidable (sixCycleShape B) := by unfold sixCycleShape; infer_instance
instance (B) : Decidable (cuts B) := by unfold cuts Separated; infer_instance

private theorem classify : ∀ B : Fin 3 → Fin 3 → Bool, rectangleFree B → sixCycleShape B ∨ cuts B := by
  decide +kernel

theorem three_normalization (I : Fin 3 → Fin 3 → Prop) [DecidableRel I]
    (C : Circuit) (free : ∀ p p' l l', p ≠ p' → l ≠ l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (mono : Monotone2 C) (correct : ∀ z, circuitFun 6 C z = true ↔ incidence I z) :
    ∃ D, Normal I C D := by
  let B (p l : Fin 3) : Bool := decide (I p l)
  have hB : rectangleFree B := by simpa [B,rectangleFree] using free
  rcases classify B hB with ⟨π,hinj,hπ⟩ | hcuts
  · have hI : I = cycleI π := by
      funext p l
      apply propext
      simpa only [B,decide_eq_true_eq,cycleI] using hπ p l
    subst I
    exact cycle_normalization π hinj C mono correct
  · apply forest_normalization I C _ mono correct
    apply forest_of_separated
    simpa only [cuts,Separated,B,decide_eq_true_eq] using hcuts

#print axioms three_normalization
end SmallIncidence
