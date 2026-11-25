import SplitTransfer
import PEqualNP.Outside.L_meta_8683

#print axioms SplitTransfer.minimum_shift
#print axioms SplitTransfer.all_budget_transfer
#print axioms SplitTransfer.extend

namespace SplitTransferExample
open PEqualNP.MetaComplexity SplitTransfer

def five : BFn 5 := fun x => (0xeeeaeae8 : ℕ).testBit (tableIndex x)
def six : BFn 6 := fun x => (4008372968 * 2^32 + 3941133032 : ℕ).testBit (tableIndex x)

set_option maxRecDepth 10000 in
theorem instance_12578 : ∀ s, HasCircuitSize 6 six s → Mono six s := by
  have factor : six = split (4 : Fin 5) five := by decide +kernel
  have essential : Essential (4 : Fin 5) five := by unfold Essential; decide +kernel
  rw [factor]
  exact all_budget_transfer 4 five essential PEqualNP.Outside.L_meta_8683

#print axioms instance_12578
end SplitTransferExample
