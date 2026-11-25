import Branch13
namespace Row12096Pilot
open Row12096Signed
set_option maxRecDepth 12000
set_option maxHeartbeats 0
/-! Sixteen admitted seven-gate subproblems of state b, checked without
assuming the remaining siblings are excluded. -/
def part0 := branch b 3 6 0 3
theorem reject0 : optimized 7 part0.1 part0.2 = false := by decide +kernel
def part1 := branch b 3 6 1 3
theorem reject1 : optimized 7 part1.1 part1.2 = false := by decide +kernel
def part2 := branch b 4 6 0 3
theorem reject2 : optimized 7 part2.1 part2.2 = false := by decide +kernel
def part3 := branch b 4 6 1 3
theorem reject3 : optimized 7 part3.1 part3.2 = false := by decide +kernel
def part4 := branch b 0 3 0 3
theorem reject4 : optimized 7 part4.1 part4.2 = false := by decide +kernel
def part5 := branch b 0 4 0 3
theorem reject5 : optimized 7 part5.1 part5.2 = false := by decide +kernel
def part6 := branch b 0 3 2 3
theorem reject6 : optimized 7 part6.1 part6.2 = false := by decide +kernel
def part7 := branch b 0 4 2 3
theorem reject7 : optimized 7 part7.1 part7.2 = false := by decide +kernel
def part8 := branch b 0 5 2 3
theorem reject8 : optimized 7 part8.1 part8.2 = false := by decide +kernel
def part9 := branch b 0 6 0 3
theorem reject9 : optimized 7 part9.1 part9.2 = false := by decide +kernel
def part10 := branch b 2 3 0 3
theorem reject10 : optimized 7 part10.1 part10.2 = false := by decide +kernel
def part11 := branch b 2 4 0 3
theorem reject11 : optimized 7 part11.1 part11.2 = false := by decide +kernel
def part12 := branch b 0 6 2 3
theorem reject12 : optimized 7 part12.1 part12.2 = false := by decide +kernel
def part13 := branch b 0 5 0 3
theorem reject13 : optimized 7 part13.1 part13.2 = false := by decide +kernel
def part14 := branch b 1 6 1 3
theorem reject14 : optimized 7 part14.1 part14.2 = false := by decide +kernel
def part15 := branch b 2 3 1 3
theorem reject15 : optimized 7 part15.1 part15.2 = false := by decide +kernel
def sixteen : List State := [part0, part1, part2, part3, part4, part5, part6, part7, part8, part9, part10, part11, part12, part13, part14, part15]
theorem groupAdmitted : sixteen.Nodup ∧ sixteen.all (admitted b) = true := by decide +kernel
theorem groupRejected : sixteen.all (fun t => !optimized 7 t.1 t.2) = true := by
  simp only [sixteen, List.all_cons, List.all_nil, Bool.not_false, Bool.true_and, reject0, reject1, reject2, reject3, reject4, reject5, reject6, reject7, reject8, reject9, reject10, reject11, reject12, reject13, reject14, reject15]
end Row12096Pilot
#print axioms Row12096Pilot.groupAdmitted
#print axioms Row12096Pilot.groupRejected
