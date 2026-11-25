import Charging
import PGSequence

namespace Row4201
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- On the plane, point 0, line 0, point 1, line 1, … is a Hamiltonian path.
Each vertex after the first edge forces a fresh OR gate, even with shared wires. -/
theorem fortyOR (C : Circuit) (hm : Monotone2 C)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔ PGSequence.accepts x) :
    40 ≤ C.gates.countP
      (fun g : Gate => GateOp.casesOn g.op false true false (fun _ => false) false) :=
  Charging.lower C hm 40 PGSequence.pref PGSequence.witness
    PGSequence.prefixMono (PGSequence.samples C computes) PGSequence.witnessNext

end Row4201
#print axioms Row4201.fortyOR
