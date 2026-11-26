import PEqualNP.Defs

namespace LocalizedFanoStar
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK

set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

def original : Circuit := ⟨[⟨.or, [8, 10]⟩,
  ⟨.or, [14, 12]⟩,
  ⟨.and, [0, 15]⟩,
  ⟨.or, [7, 10]⟩,
  ⟨.or, [17, 11]⟩,
  ⟨.and, [1, 18]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [20, 13]⟩,
  ⟨.and, [2, 21]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [23, 9]⟩,
  ⟨.and, [3, 24]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [26, 13]⟩,
  ⟨.and, [4, 27]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.or, [29, 13]⟩,
  ⟨.and, [5, 30]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.or, [32, 12]⟩,
  ⟨.and, [6, 33]⟩,
  ⟨.or, [16, 19]⟩,
  ⟨.or, [35, 22]⟩,
  ⟨.or, [36, 25]⟩,
  ⟨.or, [37, 28]⟩,
  ⟨.or, [38, 31]⟩,
  ⟨.or, [39, 34]⟩], 40⟩

def localized : Circuit := ⟨[⟨.or, [8, 10]⟩,
  ⟨.or, [14, 12]⟩,
  ⟨.and, [0, 15]⟩,
  ⟨.or, [0, 15]⟩,
  ⟨.and, [16, 17]⟩,
  ⟨.and, [16, 18]⟩,
  ⟨.or, [7, 10]⟩,
  ⟨.or, [20, 11]⟩,
  ⟨.and, [1, 21]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [23, 13]⟩,
  ⟨.and, [2, 24]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [26, 9]⟩,
  ⟨.and, [3, 27]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [29, 13]⟩,
  ⟨.and, [4, 30]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.or, [32, 13]⟩,
  ⟨.and, [5, 33]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.or, [35, 12]⟩,
  ⟨.and, [6, 36]⟩,
  ⟨.or, [19, 22]⟩,
  ⟨.or, [38, 25]⟩,
  ⟨.or, [39, 28]⟩,
  ⟨.or, [40, 31]⟩,
  ⟨.or, [41, 34]⟩,
  ⟨.or, [42, 37]⟩], 43⟩

theorem model : TopForm.IsAO2 14 original ∧ TopForm.IsAO2 14 localized ∧
    original.size = 27 ∧ localized.size = 30 := by decide

theorem localBoolean (x y : Bool) :
    ((x && y) && ((x && y) && (x || y))) = (x && y) := by cases x <;> cases y <;> rfl

theorem edge_0_1 :
    readsAtMost original 14 [0, 8] 2 = true ∧
    eachReadsAtMost localized 14 [0, 8] 2 = true ∧
    readsAtMost localized 14 [0, 8] 2 = false := by decide
theorem edge_0_3 :
    readsAtMost original 14 [0, 10] 2 = true ∧
    eachReadsAtMost localized 14 [0, 10] 2 = true ∧
    readsAtMost localized 14 [0, 10] 2 = false := by decide
theorem edge_0_5 :
    readsAtMost original 14 [0, 12] 2 = true ∧
    eachReadsAtMost localized 14 [0, 12] 2 = true ∧
    readsAtMost localized 14 [0, 12] 2 = false := by decide
theorem edge_1_0 :
    readsAtMost original 14 [1, 7] 2 = true ∧
    eachReadsAtMost localized 14 [1, 7] 2 = true ∧
    readsAtMost localized 14 [1, 7] 2 = true := by decide
theorem edge_1_3 :
    readsAtMost original 14 [1, 10] 2 = true ∧
    eachReadsAtMost localized 14 [1, 10] 2 = true ∧
    readsAtMost localized 14 [1, 10] 2 = true := by decide
theorem edge_1_4 :
    readsAtMost original 14 [1, 11] 2 = true ∧
    eachReadsAtMost localized 14 [1, 11] 2 = true ∧
    readsAtMost localized 14 [1, 11] 2 = true := by decide
theorem edge_2_2 :
    readsAtMost original 14 [2, 9] 2 = true ∧
    eachReadsAtMost localized 14 [2, 9] 2 = true ∧
    readsAtMost localized 14 [2, 9] 2 = true := by decide
theorem edge_2_3 :
    readsAtMost original 14 [2, 10] 2 = true ∧
    eachReadsAtMost localized 14 [2, 10] 2 = true ∧
    readsAtMost localized 14 [2, 10] 2 = true := by decide
theorem edge_2_6 :
    readsAtMost original 14 [2, 13] 2 = true ∧
    eachReadsAtMost localized 14 [2, 13] 2 = true ∧
    readsAtMost localized 14 [2, 13] 2 = true := by decide
theorem edge_3_0 :
    readsAtMost original 14 [3, 7] 2 = true ∧
    eachReadsAtMost localized 14 [3, 7] 2 = true ∧
    readsAtMost localized 14 [3, 7] 2 = true := by decide
theorem edge_3_1 :
    readsAtMost original 14 [3, 8] 2 = true ∧
    eachReadsAtMost localized 14 [3, 8] 2 = true ∧
    readsAtMost localized 14 [3, 8] 2 = true := by decide
theorem edge_3_2 :
    readsAtMost original 14 [3, 9] 2 = true ∧
    eachReadsAtMost localized 14 [3, 9] 2 = true ∧
    readsAtMost localized 14 [3, 9] 2 = true := by decide
theorem edge_4_1 :
    readsAtMost original 14 [4, 8] 2 = true ∧
    eachReadsAtMost localized 14 [4, 8] 2 = true ∧
    readsAtMost localized 14 [4, 8] 2 = true := by decide
theorem edge_4_4 :
    readsAtMost original 14 [4, 11] 2 = true ∧
    eachReadsAtMost localized 14 [4, 11] 2 = true ∧
    readsAtMost localized 14 [4, 11] 2 = true := by decide
theorem edge_4_6 :
    readsAtMost original 14 [4, 13] 2 = true ∧
    eachReadsAtMost localized 14 [4, 13] 2 = true ∧
    readsAtMost localized 14 [4, 13] 2 = true := by decide
theorem edge_5_0 :
    readsAtMost original 14 [5, 7] 2 = true ∧
    eachReadsAtMost localized 14 [5, 7] 2 = true ∧
    readsAtMost localized 14 [5, 7] 2 = true := by decide
theorem edge_5_5 :
    readsAtMost original 14 [5, 12] 2 = true ∧
    eachReadsAtMost localized 14 [5, 12] 2 = true ∧
    readsAtMost localized 14 [5, 12] 2 = true := by decide
theorem edge_5_6 :
    readsAtMost original 14 [5, 13] 2 = true ∧
    eachReadsAtMost localized 14 [5, 13] 2 = true ∧
    readsAtMost localized 14 [5, 13] 2 = true := by decide
theorem edge_6_2 :
    readsAtMost original 14 [6, 9] 2 = true ∧
    eachReadsAtMost localized 14 [6, 9] 2 = true ∧
    readsAtMost localized 14 [6, 9] 2 = true := by decide
theorem edge_6_4 :
    readsAtMost original 14 [6, 11] 2 = true ∧
    eachReadsAtMost localized 14 [6, 11] 2 = true ∧
    readsAtMost localized 14 [6, 11] 2 = true := by decide
theorem edge_6_5 :
    readsAtMost original 14 [6, 12] 2 = true ∧
    eachReadsAtMost localized 14 [6, 12] 2 = true ∧
    readsAtMost localized 14 [6, 12] 2 = true := by decide

#print axioms model
#print axioms edge_0_1
#print axioms edge_1_0

end LocalizedFanoStar
