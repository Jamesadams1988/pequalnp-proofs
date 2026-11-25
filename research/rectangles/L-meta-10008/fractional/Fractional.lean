import PEqualNP.Defs

namespace RectangleFractional

def rows : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]

/-- First coordinate is the row set, second is the column set, third is the
multiplicity. Translate both sets by the same amount modulo 31. -/
def seeds : List (Nat × Nat × Nat) := [(1084419, 847263758, 2), (1188867, 843328522, 2), (66125, 187580425, 1), (1081621, 579280933, 1), (53269, 713199653, 1), (1861, 195823621, 1), (147993, 441073699, 1), (4333593, 172285987, 1), (8456233, 287924490, 1), (67209, 321654795, 1), (197201, 437142021, 1), (229649, 705044999, 2), (1069585, 314724389, 1), (17309857, 560038954, 1), (459809, 940311822, 1), (8425665, 327320329, 1), (14913, 467681800, 1)]

def seedWeight (r : Nat × Nat × Nat) (i j : Nat) : Nat :=
  if r.1.testBit i && r.2.1.testBit j then r.2.2 else 0

/-- For a fixed row and column of displacement d, the unshifted seed-row
index a takes every residue exactly once as the simultaneous shift varies. -/
def displacementWeight (d : Nat) : Nat :=
  ((List.range 31).map (fun a =>
    (seeds.map (fun r => seedWeight r a ((a + d) % 31))).sum)).sum

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cyclicMatrix : ∀ i j : Fin 31,
    ((rows.getD i.val 0).testBit j.val) = (rows.getD 0 0).testBit ((j.val+31-i.val)%31) := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem multiplicities : ∀ d : Fin 31,
    displacementWeight d.val = if (rows.getD 0 0).testBit d.val then 0 else 48 := by
  decide +kernel

theorem cost : (seeds.map (fun r => r.2.2)).sum * 31 = 620 := by decide +kernel

theorem ratio : (620 : ℚ) / 48 = 155 / 12 := by norm_num

end RectangleFractional

#print axioms RectangleFractional.cyclicMatrix
#print axioms RectangleFractional.multiplicities
#print axioms RectangleFractional.cost
