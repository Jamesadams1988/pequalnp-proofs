import Rectangle
import SemanticCuts
import Concrete

namespace Row12096Rectangle
open Row12096Signed

/-- A root rectangle obstruction for each nontrivial partition rejects this
zero-slack bank at every remaining depth. -/
theorem rejectZero {ws : List W} {cert} (pass : checkAll ws cert = true)
    (k : Nat) (len : 2 ≤ ws.length) : optimized k 0 ws = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨a,b,ha,hb,p,g,u,v,pol,eq,du,dv⟩ := SemanticCuts.lastSplit ws k len hit
  exact excludes_split pass a b ha hb p g u v pol du dv eq

theorem concrete_rejected (k : Nat) : optimized k 0 Concrete.state.2 = false :=
  rejectZero Concrete.certificate_valid k (by rw [Concrete.guards.2.2]; decide)

end Row12096Rectangle
#print axioms Row12096Rectangle.rejectZero
#print axioms Row12096Rectangle.concrete_rejected
