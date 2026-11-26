import PEqualNP.Defs

namespace DepthSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A gate has zero, one or two inputs. Unused children are harmless placeholders. -/
inductive Tree (n : ℕ) where
  | leaf (i : ℕ)
  | node (op : GateOp) (a b : Tree n) (arity : Fin 3)

def Tree.eval {n} : Tree n → (Fin n → Bool) → Bool
  | .leaf i, x => (List.ofFn x).getD i false
  | .node op a b k, x => op.eval ([a.eval x, b.eval x].take k.val)

def Tree.cost {n} : Tree n → ℕ
  | .leaf _ => 0
  | .node _ a b _ => a.cost + b.cost + 1

def Tree.Good {n} : Tree n → Prop
  | .leaf _ => True
  | .node op a b _ => op ∈ ({.and, .or, .not} : Set GateOp) ∧ a.Good ∧ b.Good

end DepthSize
