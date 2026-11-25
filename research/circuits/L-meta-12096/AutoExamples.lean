import AutoRectangle
import Borderline

namespace Row12096Rectangle
open Row12096Signed

set_option maxRecDepth 24000
set_option maxHeartbeats 0

theorem allConcretePartitions : autoCheck Concrete.state.2 = true := by decide +kernel
theorem allDepths (k : ℕ) : optimized k 0 Concrete.state.2 = false :=
  autoReject allConcretePartitions k (by rw [Concrete.guards.2.2]; decide)

/-- The full root rectangularity check leaves this instance open. Direct
evaluation on its six live wires excludes the remaining five signed gates. -/
theorem needsTreeCheck : autoCheck Borderline.state.2 = false ∧
    optimized 5 0 Borderline.state.2 = false := ⟨by decide +kernel, Borderline.rejected⟩

end Row12096Rectangle
#print axioms Row12096Rectangle.allDepths
#print axioms Row12096Rectangle.needsTreeCheck
