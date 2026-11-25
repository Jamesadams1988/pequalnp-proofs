import Prune

namespace Row12096Prune
open Row12096Signed

/-- Negative positions which still agree with position i on every wire.
The bitwise intersection compares all negative sample lanes at once. -/
def collisionMask (i : Fin 256) : List W → W
  | [] => ~~~goal
  | w :: r => (if w.getLsbD i.val then w else ~~~w) &&& collisionMask i r

theorem collisionMask_spec (i j : Fin 256) (ws : List W) :
    (collisionMask i ws).getLsbD j.val = true ↔
      goal.getLsbD j.val = false ∧ ∀ w ∈ ws, w.getLsbD i.val = w.getLsbD j.val := by
  induction ws with
  | nil => simp [collisionMask, j.isLt]
  | cons w ws ih =>
    simp only [collisionMask, BitVec.getLsbD_and, Bool.and_eq_true, ih, List.forall_mem_cons]
    cases hi : w.getLsbD i.val <;> cases hj : w.getLsbD j.val <;>
      simp_all

/-- Accept any positive positions; the mask checks each one against all
negative positions. Omitting positive positions only weakens the prune. -/
def maskCollides (positives : List (Fin 256)) (ws : List W) :=
  positives.any fun i => goal.getLsbD i.val && (collisionMask i ws != 0)

def positiveRows : List (Fin 256) :=
  (List.ofFn rowPosition).filter (fun i => goal.getLsbD i.val)

theorem maskCollides_sound (positives : List (Fin 256)) (ws : List W)
    (h : maskCollides positives ws = true) (k extra : ℕ) : optimized k extra ws = false := by
  obtain ⟨i, _, hit⟩ := List.any_eq_true.mp h
  obtain ⟨hi, ne⟩ := Bool.and_eq_true_iff.mp hit
  have someBit : ∃ j : Fin 256, (collisionMask i ws).getLsbD j.val = true := by
    by_contra! empty
    have eq : collisionMask i ws = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simpa using empty ⟨j,hj⟩
    simp [eq] at ne
  obtain ⟨j, bit⟩ := someBit
  obtain ⟨hj, same⟩ := (collisionMask_spec i j ws).mp bit
  exact optimized_false_of_collision i j (by rw [hi,hj]; decide) k extra ws same

end Row12096Prune
#print axioms Row12096Prune.maskCollides_sound
