import Prune

namespace Row12096Prune
open Row12096Signed

/-- The checker may use a different set of finite exclusions at each depth. -/
def optimizedWith (dead : ℕ → ℕ → List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => if dead 0 e ws then false else optimized 0 e ws
  | k+1, e, ws =>
    if dead (k+1) e ws then false else nextLayer (optimizedWith dead k) e ws

theorem optimizedWith_eq (dead : ℕ → ℕ → List W → Bool)
    (sound : ∀ k e ws, dead k e ws = true → optimized k e ws = false)
    (k e : ℕ) (ws : List W) : optimizedWith dead k e ws = optimized k e ws := by
  induction k generalizing e ws with
  | zero => cases h : dead 0 e ws <;> simp [optimizedWith, h, sound _ _ _]
  | succ k ih =>
    cases h : dead (k+1) e ws with
    | true => simp [optimizedWith, h, sound _ _ _ h]
    | false =>
      have fn : optimizedWith dead k = optimized k := funext fun e => funext fun ws => ih e ws
      simp only [optimizedWith, h, Bool.false_eq_true, ite_false, fn]
      rfl

end Row12096Prune
#print axioms Row12096Prune.optimizedWith_eq
