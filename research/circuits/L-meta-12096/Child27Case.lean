import Branch13
namespace Row12096Pilot
open Row12096Signed
def child27 := branch parent 0 3 2 3
def child27case66 := branch child27 0 7 3 3
set_option maxHeartbeats 0
set_option maxRecDepth 12000

theorem case66Admitted : admitted parent child27 && admitted child27 child27case66 = true := by decide +kernel
theorem case66Excluded : optimized 8 child27case66.1 child27case66.2 = false := by decide +kernel
end Row12096Pilot
#print axioms Row12096Pilot.case66Admitted
#print axioms Row12096Pilot.case66Excluded
