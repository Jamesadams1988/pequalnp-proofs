import UniformChunks

namespace Row12096Compact.UniformPilot
open Row12096Signed

/-- The selected ordered banks and their positions in the filtered frontier. -/
def parent := branch first 0 4 1 3
def firstChild := branch parent 0 1 0 0
def secondChild := branch firstChild 0 4 0 3
def node := branch secondChild 1 2 1 0

theorem provenance : heads[13]? = some parent ∧
    (children parent)[0]? = some firstChild ∧
    (children firstChild)[12]? = some secondChild ∧
    (children secondChild)[55]? = some node := by decide +kernel

-- The 73 successors are covered by nineteen intervals of four states.
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem nodeRejected : optimized 7 node.1 node.2 = false := by
  apply rejectChunks 6 4 19 node (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

end Row12096Compact.UniformPilot
#print axioms Row12096Compact.UniformPilot.provenance
#print axioms Row12096Compact.UniformPilot.nodeRejected
