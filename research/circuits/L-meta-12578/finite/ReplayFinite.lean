import Std.Tactic.BVDecide.LRAT.Parser
import Std.Tactic.BVDecide.LRAT.Checker

open Std.Sat Std.Tactic.BVDecide

/-- Read the one-clause-per-line DIMACS files emitted for these instances. -/
def readCNF (path : System.FilePath) : IO (CNF Nat) := do
  let lines ← IO.FS.lines path
  let ["p", "cnf", varText, countText] := (lines[0]!).splitOn " "
    | throw <| .userError "invalid header"
  let some vars := varText.toNat? | throw <| .userError "invalid variable count"
  let some count := countText.toNat? | throw <| .userError "invalid clause count"
  let mut clauses := #[]
  for line in lines[1:] do
    let nums : List Int ← (line.splitOn " ").mapM fun token =>
      match token.toInt? with
      | some n => pure n
      | none => throw <| IO.userError "invalid number"
    let 0 :: rs := nums.reverse | throw <| IO.userError "missing end of clause"
    let mut c : CNF.Clause Nat := .empty
    for x in rs.reverse do
      unless 0 < x.natAbs && x.natAbs ≤ vars do throw <| .userError "variable out of range"
      c := c.add (x.natAbs-1) (x > 0)
    clauses := clauses.push c
  unless clauses.size == count do throw <| .userError "wrong count"
  return ⟨clauses⟩

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw <| .userError "usage: ReplayFinite.lean CNF_STEM ..."
  for stem in args do
    let cnf ← readCNF (stem ++ ".cnf")
    let proof ← LRAT.loadLRATProof (stem ++ ".lrat")
    unless LRAT.check proof cnf do throw <| .userError ("unverified " ++ stem)
    IO.println s!"{stem} accepted by Std.Tactic.BVDecide.LRAT.check ({cnf.clauses.size} clauses)"
