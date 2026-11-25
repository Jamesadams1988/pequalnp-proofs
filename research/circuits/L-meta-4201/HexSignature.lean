import Mathlib

/-! Four paid binary OR nodes, with unbounded free conjunctions before every operand
and at the final output, cannot compute the incidence graph of a six-cycle. -/
namespace Row4201.HexFour

/-- Select any conjunction of the currently available wires. Empty selection is true. -/
def meet {n} (w s : BitVec n) : Bool := (s &&& ~~~w) == 0

def step {n} (w l r : BitVec n) : BitVec (n+1) := BitVec.cons (meet w l || meet w r) w

structure Program where
  a : BitVec 6
  b : BitVec 6
  c : BitVec 7
  d : BitVec 7
  e : BitVec 8
  f : BitVec 8
  g : BitVec 9
  h : BitVec 9
  out : BitVec 10

def run (p : Program) (x : BitVec 6) : Bool :=
  meet (step (step (step (step x p.a p.b) p.c p.d) p.e p.f) p.g p.h) p.out

def agrees (p : Program) : Prop :=
  run p 9 = true ∧ run p 17 = true ∧ run p 18 = true ∧ run p 34 = true ∧ run p 36 = true ∧ run p 12 = true ∧
  run p 7 = false ∧ run p 10 = false ∧ run p 20 = false ∧ run p 33 = false ∧ run p 56 = false

end Row4201.HexFour
