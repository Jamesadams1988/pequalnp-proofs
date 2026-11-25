import SignedFrontier

namespace Row12096Rectangle.Borderline
open Row12096Signed

def state : State :=
  branch (branch (branch (branch (branch (branch first 0 4 1 3) 0 2 2 1)
    0 1 3 0) 4 5 0 3) 0 3 1 0) 1 2 1 1

set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem profile : state.1 = 0 ∧ state.2.length = 6 ∧ cuts state.2 = -1 := by decide +kernel
theorem rejected : optimized 5 0 state.2 = false := by decide +kernel

end Row12096Rectangle.Borderline
#print axioms Row12096Rectangle.Borderline.rejected
