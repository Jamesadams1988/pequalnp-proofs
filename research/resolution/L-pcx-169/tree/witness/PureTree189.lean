import Tree377
import OrdinaryTree

namespace Row169
open PEqualNP.ProofComplexity

/-- The concrete checked resolution tree for the 5-pigeon, 4-hole formula. -/
theorem pureTree189 : OrdinaryTree.PureTree (PHP 5 4) ∅ 189 :=
  tree377 _ (fun _ h => .ax h) (fun a b rule => .res a b rule)

end Row169
#print axioms Row169.pureTree189
