import CaseAudit
import PEqualNP.Outside.L_meta_17303
import PEqualNP.Outside.L_meta_17305
import PEqualNP.Outside.L_meta_17307
import PEqualNP.Outside.L_meta_17313
import PEqualNP.Outside.L_meta_17315
import PEqualNP.Outside.L_meta_17317
import PEqualNP.Outside.L_meta_17319
import PEqualNP.Outside.L_meta_17321
import PEqualNP.Outside.L_meta_17323

namespace CircuitTable11031

theorem exactMinimum :
    (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 target t → 16 ≤ t) ∧
    PEqualNP.MetaComplexity.HasCircuitSize 9 target 16 ∧
    ¬ (¬ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) t → 16 ≤ t)) :=
  assemble
    PEqualNP.Outside.L_meta_17303
    PEqualNP.Outside.L_meta_17305
    PEqualNP.Outside.L_meta_17307
    PEqualNP.Outside.L_meta_17313
    PEqualNP.Outside.L_meta_17315
    PEqualNP.Outside.L_meta_17317
    PEqualNP.Outside.L_meta_17319
    PEqualNP.Outside.L_meta_17321
    PEqualNP.Outside.L_meta_17323

end CircuitTable11031
