import SignedFrontier

/-! Finite branch checks for the signed circuit search of L-meta-12096.
Branch numbers in this note are zero based. -/
namespace Row12096Pilot
open Row12096Signed

/-- A state with no successful output and no admitted successor fails for every budget. -/
theorem rejectEmpty (s : State)
    (covered : nextLayer (outsideList []) s.1 s.2 = false) (d : ℕ) :
    optimized d s.1 s.2 = false := by
  cases d with
  | zero =>
    change (s.2 == [goal] || s.2 == [~~~goal]) = false
    exact (Bool.or_eq_false_iff.mp covered).1
  | succ d =>
    exact rejectLayer (k := d) (s := s) (states := []) covered (by simp)

def parent := branch first 0 4 1 3
theorem parentInFrontier : heads[13]? = some parent := by decide +kernel

def a := branch parent 0 1 0 0
def b := branch a 0 1 1 3
def c := branch b 3 6 0 3
def terminal := branch c 0 3 3 0

set_option maxRecDepth 10000
set_option maxHeartbeats 0
def admitted (s t : State) : Bool := nextLayer (fun e ws => (e,ws) == t) s.1 s.2
theorem checkedPath : admitted parent a && admitted a b && admitted b c && admitted c terminal = true := by
  decide +kernel

theorem completeSevenGateBranch : optimized 7 c.1 c.2 = false := by decide +kernel

theorem terminalHasNoChildren :
    nextLayer (outsideList []) terminal.1 terminal.2 = false := by decide +kernel
theorem terminalAllBudgets (d : ℕ) : optimized d terminal.1 terminal.2 = false :=
  rejectEmpty terminal terminalHasNoChildren d

end Row12096Pilot
#print axioms Row12096Pilot.checkedPath
#print axioms Row12096Pilot.completeSevenGateBranch
#print axioms Row12096Pilot.terminalAllBudgets
