import CofactorBound
import PEqualNP.Outside.L_meta_12184

namespace ThresholdBatch
open CofactorBound
open PEqualNP.Outside.L_meta_12184
open PEqualNP.MetaComplexity

def table {n : ℕ} (mask : ℕ) (x : Fin n → Bool) : Bool :=
  mask.testBit (∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0)

theorem twoFloor : Lower (table (n := 4) 0xfee8) 7 := by
  have image : (table (n := 4) 0xfee8) = Transfer.small := funext (by decide +kernel)
  rw [image]
  exact Foundation.lower

theorem threeFloor : Lower (table (n := 4) 0xe880) 7 := by
  intro s h
  have dual := Transfer.dual_size (table (n := 4) 0xe880) ⟨fun _ => true, by decide +kernel⟩ s h
  have image : (fun x : Fin 4 → Bool => !(table 0xe880 (fun i => !x i))) = Transfer.small :=
    funext (by decide +kernel)
  rw [image] at dual
  exact Foundation.lower s dual

namespace Row12096

def six : BFn 6 := table (4269866496 * 2^32 + 4261472256)
def five : BFn 5 := table 4278124264
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 3 false (![0,1,2,0,3])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 3 true (![0,1,2,0,3,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row12096

namespace Row15101

def six : BFn 6 := table (2827520136 * 2^32 + 2826993664)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15101

namespace Row15113

def six : BFn 6 := table (2863179912 * 2^32 + 2827520136)
def five : BFn 5 := table 4276808362
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 0 false (![0,0,1,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15113

namespace Row15127

def six : BFn 6 := table (2863311528 * 2^32 + 2863179912)
def five : BFn 5 := table 4294901482
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 0 false (![0,0,1,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row15127

namespace Row15129

def six : BFn 6 := table (3900745856 * 2^32 + 3363866752)
def five : BFn 5 := table 3900754048
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (13 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15129

namespace Row15139

def six : BFn 6 := table (3901270152 * 2^32 + 3900745856)
def five : BFn 5 := table 3901286528
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15139

namespace Row15147

def six : BFn 6 := table (3901284480 * 2^32 + 3900760192)
def five : BFn 5 := table 3901286528
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (11 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15147

namespace Row15151

def six : BFn 6 := table (3901286528 * 2^32 + 3901284480)
def five : BFn 5 := table 3900760192
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (11 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15151

namespace Row15209

def six : BFn 6 := table (3903383688 * 2^32 + 3902859392)
def five : BFn 5 := table 3901286528
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15209

namespace Row15287

def six : BFn 6 := table (3937053354 * 2^32 + 3900745856)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15287

namespace Row15345

def six : BFn 6 := table (3937069184 * 2^32 + 3937060992)
def five : BFn 5 := table 3900754048
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (13 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15345

namespace Row15353

def six : BFn 6 := table (3937069192 * 2^32 + 3937069184)
def five : BFn 5 := table 3901286528
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15353

namespace Row15379

def six : BFn 6 := table (3938511040 * 2^32 + 3934316672)
def five : BFn 5 := table 3904956544
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15379

namespace Row15529

def six : BFn 6 := table (3941132992 * 2^32 + 3941116544)
def five : BFn 5 := table 3904956544
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 3 false (![0,1,2,0,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15529

namespace Row15769

def six : BFn 6 := table (4008372896 * 2^32 + 3941264032)
def five : BFn 5 := table 4276678376
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row15769

namespace Row15773

def six : BFn 6 := table (4008372906 * 2^32 + 3937053354)
def five : BFn 5 := table 2826993664
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 0 true (![0,0,1,2,3])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (15 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row15773

namespace Row15845

def six : BFn 6 := table (4008372960 * 2^32 + 4008372896)
def five : BFn 5 := table 4276944616
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row15845

namespace Row15949

def six : BFn 6 := table (4008636138 * 2^32 + 4008372906)
def five : BFn 5 := table 2863179904
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 0 true (![0,0,1,2,3])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row15949

namespace Row16119

def six : BFn 6 := table (3941264000 * 2^32 + 3941132928)
def five : BFn 5 := table 3934316672
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 3 false (![0,1,2,0,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16119

namespace Row16125

def six : BFn 6 := table (3941264008 * 2^32 + 3934841344)
def five : BFn 5 := table 4008241376
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 2 false (![0,1,0,2,3])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 true (![0,1,0,2,3,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16125

namespace Row16131

def six : BFn 6 := table (3941264008 * 2^32 + 3937053184)
def five : BFn 5 := table 4008372896
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 true (![0,0,1,2,3])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (28 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16131

namespace Row16167

def six : BFn 6 := table (3941264042 * 2^32 + 3938510976)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16167

namespace Row16175

def six : BFn 6 := table (3941264042 * 2^32 + 3941132928)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 3 false (![0,1,2,0,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16175

namespace Row16187

def six : BFn 6 := table (3941264072 * 2^32 + 3939027136)
def five : BFn 5 := table 4294638248
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 false (![0,0,1,2,3])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16187

namespace Row16195

def six : BFn 6 := table (3941264104 * 2^32 + 3941132992)
def five : BFn 5 := table 4294901496
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 2 false (![0,1,0,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (8 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16195

namespace Row16215

def six : BFn 6 := table (4007717088 * 2^32 + 3907051744)
def five : BFn 5 := table 3766517760
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 2 true (![0,1,0,2,3])
  · exact ⟨fun i => (11 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (15 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16215

namespace Row16223

def six : BFn 6 := table (4007717088 * 2^32 + 3940589728)
def five : BFn 5 := table 4243385480
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 2 true (![0,1,0,2,3])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (20 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16223

namespace Row16255

def six : BFn 6 := table (4008241376 * 2^32 + 3941132512)
def five : BFn 5 := table 3900745856
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (14 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16255

namespace Row16257

def six : BFn 6 := table (4008241376 * 2^32 + 4007717088)
def five : BFn 5 := table 3900760192
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (11 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16257

namespace Row16267

def six : BFn 6 := table (4008241384 * 2^32 + 4008241376)
def five : BFn 5 := table 3901286528
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16267

namespace Row16269

def six : BFn 6 := table (4008241824 * 2^32 + 3941132960)
def five : BFn 5 := table 4276678376
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16269

namespace Row16271

def six : BFn 6 := table (4008241824 * 2^32 + 4007717536)
def five : BFn 5 := table 4276681960
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16271

namespace Row16273

def six : BFn 6 := table (4008241824 * 2^32 + 4008225440)
def five : BFn 5 := table 4276682408
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (17 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16273

namespace Row16287

def six : BFn 6 := table (4008241832 * 2^32 + 4008241824)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16287

namespace Row16321

def six : BFn 6 := table (4008241888 * 2^32 + 4008241376)
def five : BFn 5 := table 3902859392
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16321

namespace Row16323

def six : BFn 6 := table (4008241888 * 2^32 + 4008241824)
def five : BFn 5 := table 4276944616
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16323

namespace Row16361

def six : BFn 6 := table (4008372896 * 2^32 + 3937069728)
def five : BFn 5 := table 4276677352
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16361

namespace Row16363

def six : BFn 6 := table (4008372896 * 2^32 + 3940608672)
def five : BFn 5 := table 4276677864
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16363

namespace Row16365

def six : BFn 6 := table (4008372896 * 2^32 + 3941263872)
def five : BFn 5 := table 4276678368
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16365

namespace Row16367

def six : BFn 6 := table (4008372896 * 2^32 + 4008241824)
def five : BFn 5 := table 4008241824
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 true (![0,0,1,2,3])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 5 false (![0,1,2,3,4,0])
  · exact ⟨fun i => (17 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16367

namespace Row16377

def six : BFn 6 := table (4008372904 * 2^32 + 4008372896)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16377

namespace Row16405

def six : BFn 6 := table (4008372906 * 2^32 + 3974686880)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16405

namespace Row16411

def six : BFn 6 := table (4008372906 * 2^32 + 4008241824)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16411

namespace Row16419

def six : BFn 6 := table (4008372928 * 2^32 + 4008372864)
def five : BFn 5 := table 4276944616
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16419

namespace Row16443

def six : BFn 6 := table (4008372960 * 2^32 + 3940606176)
def five : BFn 5 := table 4276939980
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 false (![0,0,1,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (4 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16443

namespace Row16529

def six : BFn 6 := table (4008372970 * 2^32 + 4006144192)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16529

namespace Row16537

def six : BFn 6 := table (4008372970 * 2^32 + 4008241376)
def five : BFn 5 := table 3937069184
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 2 false (![0,1,0,2,3,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16537

namespace Row16545

def six : BFn 6 := table (4008372970 * 2^32 + 4008372896)
def five : BFn 5 := table 4277075688
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16545

namespace Row16573

def six : BFn 6 := table (4008373984 * 2^32 + 4008372896)
def five : BFn 5 := table 4277993192
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16573

namespace Row16581

def six : BFn 6 := table (4008373992 * 2^32 + 4008373440)
def five : BFn 5 := table 4294901736
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 3 false (![0,1,2,0,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16581

namespace Row16591

def six : BFn 6 := table (4008636138 * 2^32 + 4008372928)
def five : BFn 5 := table 4294901484
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 false (![0,0,1,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (4 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16591

namespace Row16595

def six : BFn 6 := table (4008636138 * 2^32 + 4008372960)
def five : BFn 5 := table 4294901484
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 false (![0,0,1,2,3])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 1 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (4 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16595

namespace Row16597

def six : BFn 6 := table (4276677352 * 2^32 + 4008241896)
def five : BFn 5 := table 4276678376
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16597

namespace Row16599

def six : BFn 6 := table (4276677352 * 2^32 + 4243122408)
def five : BFn 5 := table 4276681960
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16599

namespace Row16601

def six : BFn 6 := table (4276677352 * 2^32 + 4274580168)
def five : BFn 5 := table 4276682440
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16601

namespace Row16603

def six : BFn 6 := table (4276678368 * 2^32 + 4008242912)
def five : BFn 5 := table 4276678376
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16603

namespace Row16605

def six : BFn 6 := table (4276678368 * 2^32 + 4209568480)
def five : BFn 5 := table 4276681448
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16605

namespace Row16607

def six : BFn 6 := table (4276678376 * 2^32 + 4276677352)
def five : BFn 5 := table 4276677352
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 5 false (![0,1,2,3,4,0])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16607

namespace Row16609

def six : BFn 6 := table (4276678376 * 2^32 + 4276678368)
def five : BFn 5 := table 4276678368
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 5 false (![0,1,2,3,4,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16609

namespace Row16611

def six : BFn 6 := table (4276808362 * 2^32 + 3941264042)
def five : BFn 5 := table 3900737664
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (13 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16611

namespace Row16635

def six : BFn 6 := table (4276808426 * 2^32 + 4276677352)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16635

namespace Row16663

def six : BFn 6 := table (4276808936 * 2^32 + 4276677864)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16663

namespace Row16679

def six : BFn 6 := table (4276809440 * 2^32 + 4276678368)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16679

namespace Row16693

def six : BFn 6 := table (4276809448 * 2^32 + 4276678376)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16693

namespace Row16741

def six : BFn 6 := table (4276809450 * 2^32 + 4276669640)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16741

namespace Row16743

def six : BFn 6 := table (4276809450 * 2^32 + 4276677864)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (9 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16743

namespace Row16745

def six : BFn 6 := table (4276809450 * 2^32 + 4276678368)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16745

namespace Row16751

def six : BFn 6 := table (4276809450 * 2^32 + 4276808362)
def five : BFn 5 := table 3903383680
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16751

namespace Row16765

def six : BFn 6 := table (4276813000 * 2^32 + 4276681928)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16765

namespace Row16783

def six : BFn 6 := table (4276813544 * 2^32 + 4276800712)
def five : BFn 5 := table 4276669640
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16783

namespace Row16785

def six : BFn 6 := table (4276813544 * 2^32 + 4276809448)
def five : BFn 5 := table 4276678376
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16785

namespace Row16787

def six : BFn 6 := table (4276813544 * 2^32 + 4276813000)
def five : BFn 5 := table 4276681928
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16787

namespace Row16861

def six : BFn 6 := table (4277071598 * 2^32 + 4276678376)
def five : BFn 5 := table 4277075688
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16861

namespace Row16879

def six : BFn 6 := table (4277074602 * 2^32 + 4276808362)
def five : BFn 5 := table 3938510976
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row16879

namespace Row16943

def six : BFn 6 := table (4277074666 * 2^32 + 4276681448)
def five : BFn 5 := table 4277075688
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16943

namespace Row16971

def six : BFn 6 := table (4277075680 * 2^32 + 4276682464)
def five : BFn 5 := table 4277075688
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 true (![0,1,2,3,0,4])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16971

namespace Row16987

def six : BFn 6 := table (4277075688 * 2^32 + 4276813544)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 5 false (![0,1,2,3,4,0])
  · exact ⟨fun i => (18 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16987

namespace Row16989

def six : BFn 6 := table (4277075688 * 2^32 + 4277072096)
def five : BFn 5 := table 4276678880
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16989

namespace Row16991

def six : BFn 6 := table (4277075688 * 2^32 + 4277074664)
def five : BFn 5 := table 4276681448
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16991

namespace Row16993

def six : BFn 6 := table (4277075688 * 2^32 + 4277075680)
def five : BFn 5 := table 4276682464
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 true (![0,1,2,3,0])
  · exact ⟨fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row16993

namespace Row17007

def six : BFn 6 := table (4277075690 * 2^32 + 4276812458)
def five : BFn 5 := table 3941132480
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 0 true (![0,0,1,2,3])
  · exact ⟨fun i => (10 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row17007

namespace Row17031

def six : BFn 6 := table (4277075690 * 2^32 + 4277070506)
def five : BFn 5 := table 3941132928
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 3 false (![0,1,2,0,3])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row17031

namespace Row17045

def six : BFn 6 := table (4277075690 * 2^32 + 4277075688)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row17045

namespace Row17069

def six : BFn 6 := table (4278124202 * 2^32 + 4277992576)
def five : BFn 5 := table 4294967016
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 true (![0,0,1,2,3,4])
  · exact ⟨fun i => (6 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row17069

namespace Row17073

def six : BFn 6 := table (4278124266 * 2^32 + 4276813482)
def five : BFn 5 := table 4008241376
def four : BFn 4 := table 59520

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 2 false (![0,1,0,2,3])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (7 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 threeFloor

#print axioms nine
end Row17073

namespace Row17075

def six : BFn 6 := table (4278124266 * 2^32 + 4277071530)
def five : BFn 5 := table 4008241824
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 1 true (![0,0,1,2,3])
  · exact ⟨fun i => (12 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 0 false (![0,0,1,2,3,4])
  · exact ⟨fun i => (0 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (5 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row17075

namespace Row17087

def six : BFn 6 := table (4278124266 * 2^32 + 4277993192)
def five : BFn 5 := table 4276813544
def four : BFn 4 := table 65256

set_option maxRecDepth 16384 in
theorem five_bound (k : ℕ) (floor : Lower four k) : Lower five (k+1) := by
  apply ofPinnedImage (g := four) 4 false (![0,1,2,3,0])
  · exact ⟨fun i => (1 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact floor

set_option maxRecDepth 16384 in
theorem six_bound (k : ℕ) (floor : Lower four k) : Lower six (k+1+1) := by
  apply ofPinnedImage (g := five) 4 false (![0,1,2,3,0,4])
  · exact ⟨fun i => (2 : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => (0 : ℕ).testBit i, fun i => (3 : ℕ).testBit i, by decide +kernel⟩
  · exact five_bound k floor

theorem nine : Lower six 9 := six_bound 7 twoFloor

#print axioms nine
end Row17087

end ThresholdBatch
