import CompactLayer

namespace Row12096Compact
open Row12096Signed

/-- Intervals share the same width. The final interval may be short. -/
theorem coverChunks (d width : Nat) (ss : List State) (start count : Nat)
    (bound : ss.length ≤ start + count * width)
    (h : ∀ i : Fin count, rejected d ((ss.drop (start+i.val*width)).take width) = true) :
    rejected d (ss.drop start) = true := by
  induction count generalizing start with
  | zero =>
    have empty : ss.drop start = [] := List.drop_eq_nil_iff.mpr (by simpa using bound)
    rw [empty]
    rfl
  | succ n ih =>
    apply mergeAt d start width ss
    · simpa using h 0
    · apply ih (start+width)
      · simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
      · intro i
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h i.succ

/-- A parent certificate needs one length bound and one finite family of exact interval
checks; proof source size per parent is independent of the number of intervals. -/
theorem rejectChunks (d width count : Nat) (s : State) (miss : doneAt s = false)
    (lengthBound : (children s).length ≤ count * width)
    (check : ∀ i : Fin count, rejected d (((children s).drop (i.val * width)).take width) = true) :
    optimized (d+1) s.1 s.2 = false := by
  apply rejectChildren d s miss
  apply coverChunks d width (children s) 0 count (by simpa using lengthBound)
  simpa using check

end Row12096Compact
#print axioms Row12096Compact.rejectChunks
