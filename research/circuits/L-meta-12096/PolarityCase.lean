import Polarity

namespace Row12096Polarity.Case17
open Row12096Signed

def head := branch first 0 4 1 3
def child := branch head 0 2 2 1
def s1 := branch child 0 1 0 2
def s2 := branch s1 1 5 0 2
def s3 := branch s2 1 3 1 2
def rows : Fin 4 → Fin 256 := ![8,239,6,216]
def admitted (s t : State) : Bool := nextLayer (fun e ws => (e,ws) == t) s.1 s.2

set_option maxRecDepth 10000
theorem path : heads[13]? = some head ∧
    (admitted head child && admitted child s1 && admitted s1 s2 && admitted s2 s3) = true ∧
    s3.1 = 0 ∧ s3.2.length = 7 := by decide +kernel

theorem weights : (total (fun x => polarity (project rows x)) s3.2,
    polarity (project rows goal), polarity (project rows (~~~goal))) = (1,2,2) := by decide +kernel

/-- Both zero-to-one transitions, rows 56→57 and 53→44, are supported
exclusively by the same live wire. Its polarities on them are opposite. -/
theorem excluded (d : ℕ) : optimized d s3.1 s3.2 = false := by
  rw [path.2.2.1]
  apply polarityLower rows
  all_goals decide +kernel

end Row12096Polarity.Case17
#print axioms Row12096Polarity.Case17.excluded
