import Prune

namespace Row12096Prune.Head13
open Row12096Signed

def head : State := branch first 0 4 1 3
def child : State := branch head 0 1 2 1
def descendant : State := branch child 1 2 2 0

set_option maxRecDepth 12000 in
theorem path : heads.getD 13 first = head ∧ head.1 = 4 ∧ child.1 = 3 ∧ descendant.1 = 3 ∧
    cuts head.2 = -1 ∧ cuts child.2 = -1 ∧ cuts descendant.2 = -1 := by decide +kernel

theorem labels : rowPosition 8 = 124 ∧ rowPosition 25 = 156 ∧
    goal.getLsbD 124 = false ∧ goal.getLsbD 156 = true := by decide +kernel

theorem collision : collides [(124,156)] descendant.2 = true := by decide +kernel

/-- The original paired mask accepts this bank. Rows 8 and 25 agree on
every available wire, but their outputs differ. -/
theorem excluded (k extra : ℕ) : optimized k extra descendant.2 = false :=
  collides_sound [(124,156)] descendant.2 collision k extra

end Row12096Prune.Head13
#print axioms Row12096Prune.Head13.excluded
