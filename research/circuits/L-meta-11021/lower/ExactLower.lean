import CaseAudit
import PEqualNP.Outside.L_meta_17103
import PEqualNP.Outside.L_meta_17269
import PEqualNP.Outside.L_meta_17271
import PEqualNP.Outside.L_meta_17273
import PEqualNP.Outside.L_meta_17275
import PEqualNP.Outside.L_meta_17277
import PEqualNP.Outside.L_meta_17279
import PEqualNP.Outside.L_meta_17281
import PEqualNP.Outside.L_meta_17283

namespace CircuitTable11021

theorem positive : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 16 ≤ t :=
  positiveOfCases
    PEqualNP.Outside.L_meta_17103
    PEqualNP.Outside.L_meta_17269
    PEqualNP.Outside.L_meta_17271
    PEqualNP.Outside.L_meta_17273
    PEqualNP.Outside.L_meta_17275
    PEqualNP.Outside.L_meta_17277
    PEqualNP.Outside.L_meta_17279
    PEqualNP.Outside.L_meta_17281
    PEqualNP.Outside.L_meta_17283

theorem refutation : ¬ (¬ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 16 ≤ t)) := fun h => h positive

#print axioms refutation
end CircuitTable11021
