import PEqualNP.Outside.L_meta_8657

/-!
Theorem `profile` gives exact unrestricted and monotone gate counts for all
twelve single-input restrictions of the six-input truth table in L-meta-15174.
For each coordinate, the remaining variables retain their original order.

The lower bounds instantiate Noptus's live-wire search from L-meta-8657.
Each sample pairs a zero row with a one row. The samples include all pairs of
maximal zeros and minimal ones and all sensitive, single-coordinate edges.
The theorem also supplies an explicit monotone circuit for each face.
-/

namespace Row15174Faces
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8657

theorem lowerOfSamples (T k d : ℕ) (rs xs : List ℕ)
    (hnc : fn T (fun _ => false) ≠ fn T (fun _ => true))
    (hm : mask k = 2^rs.length - 1)
    (hi : (List.ofFn fun i : Fin 5 => fun x : Fin 5 → Bool => x i).map (fun a => encL a rs) = xs)
    (hy : encL (fn T) rs = goal k)
    (hno : ∀ zs ∈ xs.sublists, (((cov k zs &&& lo k) != lo k) ||
      (List.range (d+1)).all (fun t => !search k t zs)) = true) :
    ∀ s, HasCircuitSize 5 (fn T) s → d + 1 ≤ s := by
  intro s h
  by_contra! hs
  obtain ⟨t, ht, ws, hsub, hr⟩ := exists_run (fn T) ⟨_, _, hnc⟩ s h
  have he : NatRun (mask k) (encL (fn T) rs) t (ws.map fun a => encL a rs) :=
    Run.map (fun a : BFn 5 => encL a rs) (fun a => by rw [hm]; exact encL_inv a rs)
      (fun a b => encL_and a b rs) (fun a b => encL_or a b rs) hr
  rw [hy] at he
  have hsub' := hsub.map (fun a => encL a rs)
  rw [hi] at hsub'
  have hn := hno _ (List.mem_sublists.2 hsub')
  simp only [required he, bne_self_eq_false, Bool.false_or, List.all_eq_true] at hn
  have hnt := hn t (List.mem_range.mpr (by omega))
  simp [search_ok he] at hnt

def full (x : Fin 6 → Bool) := Nat.testBit (3903367336 * 2^32 + 3892348928)
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def face (p : Fin 6) (b : Bool) (x : Fin 5 → Bool) := full (p.insertNth b x)

def Exact (f : BFn 5) (size : ℕ) : Prop :=
  (∀ s, HasCircuitSize 5 f s → size ≤ s) ∧
    ∃ C : Circuit, Monotone2 C ∧ C.size = size ∧ ∀ x, C.eval (List.ofFn x) = f x

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace X0B0
def rows : List Nat := [23, 27, 29, 30, 7, 11, 13, 14, 23, 27, 29, 30, 15, 15, 15, 15, 15, 15, 15, 15, 31, 31, 31, 31]
def inputs : List Nat := [0xfff777,0xfffbbb,0xfffddd,0xfffeee,0xf00f0f]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.and, [2,3]⟩,⟨.and, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 0 false) 3 := by
  have heq : face 0 false = fn 0x80008000 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0x80008000 12 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X0B0

namespace X0B1
def rows : List Nat := [6, 6, 6, 6, 11, 11, 11, 11, 28, 28, 28, 28, 1, 1, 2, 3, 3, 4, 6, 6, 9, 9, 10, 10, 11, 11, 12, 12, 16, 16, 20, 20, 24, 24, 28, 28, 5, 14, 17, 18, 5, 14, 17, 18, 5, 14, 17, 18, 5, 17, 18, 7, 19, 5, 7, 22, 13, 25, 14, 26, 15, 27, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30]
def inputs : List Nat := [0x55737b55500331b0f0,0xaabcdcaaa003cdc0ff,0xccd5e9333ccc0e0f0f,0xf0ff00222f0ff00ff0,0xff2a96cccff0000f00]
def circuit : Circuit := ⟨[⟨.or, [0,1]⟩,⟨.or, [0,3]⟩,⟨.and, [2,6]⟩,⟨.or, [4,7]⟩,⟨.and, [5,8]⟩], 9⟩

theorem exactSize : Exact (face 0 true) 5 := by
  have heq : face 0 true = fn 0xeeeee0a0 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeeeee0a0 36 4 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X0B1

namespace X1B0
def rows : List Nat := [7, 7, 11, 11, 29, 29, 30, 30, 3, 7, 11, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 15, 19, 15, 19, 15, 19, 15, 19, 19, 23, 27, 15, 15, 19, 19, 23, 23, 27, 27, 31, 31]
def inputs : List Nat := [0x3ffffeaaf3f,0x3fffff557cf,0x3334ab99af3,0x3c38abe1cfc,0x3fcf55fe0f0]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.and, [2,3]⟩,⟨.or, [4,6]⟩,⟨.and, [5,7]⟩], 8⟩

theorem exactSize : Exact (face 1 false) 4 := by
  have heq : face 1 false = fn 0x88888000 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0x88888000 21 3 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X1B0

namespace X1B1
def rows : List Nat := [11, 11, 11, 22, 22, 22, 26, 26, 26, 28, 28, 28, 1, 1, 3, 3, 4, 6, 6, 9, 9, 10, 11, 11, 12, 12, 16, 18, 20, 22, 22, 24, 26, 26, 28, 28, 5, 14, 17, 5, 14, 17, 5, 14, 17, 5, 14, 17, 5, 17, 7, 19, 5, 7, 14, 13, 25, 14, 15, 27, 13, 14, 17, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x5bddbfb6d000d8f007,0xb6ae6c492368e6c1ff,0xe736f56dbc73070e38,0xfc3fc0492f83f80fc7,0xffc90a924ffc000ff8]
def circuit : Circuit := ⟨[⟨.and, [0,4]⟩,⟨.and, [1,3]⟩,⟨.or, [0,6]⟩,⟨.or, [2,5]⟩,⟨.and, [7,8]⟩], 9⟩

theorem exactSize : Exact (face 1 true) 5 := by
  have heq : face 1 true = fn 0xeaaae0a0 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeaaae0a0 36 4 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X1B1

namespace X2B0
def rows : List Nat := [11, 11, 29, 29, 30, 30, 3, 3, 5, 6, 11, 11, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 7, 19, 7, 19, 7, 19, 7, 19, 7, 7, 15, 27, 15, 15, 19, 19, 23, 23, 27, 27, 31, 31]
def inputs : List Nat := [0xfffffd55dcf,0xfffffeaaef3,0xccdd573333c,0xf0f003c3c3f,0xff22abfc03c]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [2,4]⟩,⟨.and, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 2 false) 3 := by
  have heq : face 2 false = fn 0x88888080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0x88888080 22 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X2B0

namespace X2B1
def rows : List Nat := [5, 5, 5, 5, 11, 11, 11, 11, 22, 22, 22, 22, 26, 26, 26, 26, 28, 28, 28, 28, 1, 3, 3, 5, 6, 6, 9, 9, 10, 11, 11, 12, 12, 16, 18, 20, 22, 22, 24, 26, 26, 28, 28, 7, 13, 14, 17, 7, 13, 14, 17, 7, 13, 14, 17, 7, 13, 14, 17, 7, 13, 14, 17, 17, 7, 19, 21, 7, 14, 13, 25, 14, 15, 27, 13, 14, 17, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x16f76fddddd8006cf000ff,0x2dab9b2aaaa9b47360fff0,0x39cdbd3bbbbe39838f0f0f,0x3f0ff0333337c1fc0ff0f0,0x3ff246c44447fe000fff00]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.and, [0,4]⟩,⟨.and, [2,6]⟩,⟨.or, [3,5]⟩,⟨.and, [8,9]⟩,⟨.or, [7,10]⟩], 11⟩

theorem exactSize : Exact (face 2 true) 7 := by
  have heq : face 2 true = fn 0xeaaae080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeaaae080 43 6 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X2B1

namespace X3B0
def rows : List Nat := [15, 15, 25, 25, 30, 30, 3, 5, 7, 11, 13, 15, 17, 17, 18, 20, 22, 25, 25, 26, 28, 30, 19, 21, 19, 21, 19, 21, 19, 21, 23, 27, 29, 31, 19, 21, 19, 21, 23, 27, 29, 27, 29, 31]
def inputs : List Nat := [0xfffffc63fcf,0xad6d5694b73,0xd6b6ab18db3,0xf83803e0e3f,0xffffffff03c]
def circuit : Circuit := ⟨[⟨.and, [0,4]⟩,⟨.or, [1,2]⟩,⟨.and, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 3 false) 3 := by
  have heq : face 3 false = fn 0xa8a80000 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xa8a80000 22 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X3B0

namespace X3B1
def rows : List Nat := [5, 5, 5, 5, 22, 22, 22, 22, 25, 25, 25, 25, 26, 26, 26, 26, 28, 28, 28, 28, 1, 2, 5, 6, 6, 9, 9, 10, 10, 12, 12, 17, 17, 18, 20, 22, 22, 25, 25, 26, 26, 28, 28, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 3, 7, 7, 14, 11, 13, 11, 14, 13, 14, 19, 21, 19, 21, 23, 30, 27, 29, 27, 30, 29, 30]
def inputs : List Nat := [0x177d77ddddd86186500f0f,0x2dd6dfaaaaa99a19a0f0f0,0x3aebae7777761c61cf00ff,0x3f83f8333337e07e0fff00,0x3ffc00444447ff800ffff0]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.and, [0,4]⟩,⟨.and, [2,6]⟩,⟨.or, [3,7]⟩,⟨.and, [8,9]⟩,⟨.or, [5,10]⟩], 11⟩

theorem exactSize : Exact (face 3 true) 7 := by
  have heq : face 3 true = fn 0xe8a8e888 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xe8a8e888 43 6 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X3B1

namespace X4B0
def rows : List Nat := [7, 7, 7, 13, 13, 13, 25, 25, 25, 30, 30, 30, 3, 3, 5, 7, 7, 9, 10, 13, 13, 14, 17, 17, 18, 20, 22, 25, 25, 26, 28, 30, 11, 19, 21, 11, 19, 21, 11, 19, 21, 11, 19, 21, 11, 19, 21, 15, 23, 11, 11, 15, 29, 15, 19, 21, 19, 21, 23, 27, 29, 27, 29, 31]
def inputs : List Nat := [0xffffffff18dbf1ff,0xad6fb6dba525be07,0xd6b9c924c639ce3f,0xf83e9249f83e0ff8,0xffd16db6ffc00fc0]
def circuit : Circuit := ⟨[⟨.or, [1,2]⟩,⟨.and, [0,5]⟩,⟨.and, [1,3]⟩,⟨.or, [4,7]⟩,⟨.and, [6,8]⟩], 9⟩

theorem exactSize : Exact (face 4 false) 5 := by
  have heq : face 4 false = fn 0xa8a88800 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xa8a88800 32 4 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X4B0

namespace X4B1
def rows : List Nat := [7, 7, 7, 7, 7, 22, 22, 22, 22, 22, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 3, 3, 5, 5, 6, 7, 7, 9, 9, 10, 10, 12, 12, 17, 17, 18, 20, 22, 22, 25, 25, 26, 26, 28, 28, 11, 13, 14, 19, 21, 11, 13, 14, 19, 21, 11, 13, 14, 19, 21, 11, 13, 14, 19, 21, 11, 13, 14, 19, 21, 11, 19, 13, 21, 14, 15, 23, 11, 13, 11, 14, 13, 14, 19, 21, 19, 21, 23, 30, 27, 29, 27, 30, 29, 30]
def inputs : List Nat := [0x5df5f7ef7bdec30c3de007c1f,0xb75b79b5ad6b4cd0ce60f83ff,0xebaebe5ad6b5b0e30f9f003ff,0xfe0fda9ce739ff03f01fffc00,0xfff0256318c63ffc001ffffe0]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.and, [0,4]⟩,⟨.or, [2,5]⟩,⟨.and, [3,6]⟩,⟨.or, [7,9]⟩,⟨.and, [8,10]⟩], 11⟩

theorem exactSize : Exact (face 4 true) 7 := by
  have heq : face 4 true = fn 0xe8a8e800 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xe8a8e800 50 6 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X4B1

namespace X5B0
def rows : List Nat := [13, 13, 13, 14, 14, 14, 23, 23, 23, 25, 25, 25, 26, 26, 26, 28, 28, 28, 3, 7, 9, 10, 13, 14, 19, 21, 22, 23, 25, 26, 11, 29, 30, 11, 29, 30, 11, 29, 30, 11, 29, 30, 11, 29, 30, 11, 29, 30, 11, 15, 11, 11, 15, 15, 27, 29, 30, 31, 27, 27]
def inputs : List Nat := [0xeff6db6db5c0fc7,0xf7fb6db6dac71f8,0x3b2db6d8ecb81ff,0xffffffff0f3fe3f,0xfc0db6dbf03ffc0]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.and, [2,4]⟩,⟨.and, [3,6]⟩,⟨.or, [5,7]⟩,⟨.and, [8,9]⟩], 10⟩

theorem exactSize : Exact (face 5 false) 6 := by
  have heq : face 5 false = fn 0xe8008800 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xe8008800 30 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X5B0

namespace X5B1
def rows : List Nat := [14, 14, 14, 22, 22, 22, 25, 25, 25, 26, 26, 26, 28, 28, 28, 1, 1, 2, 4, 6, 9, 9, 10, 12, 14, 17, 17, 18, 20, 22, 25, 25, 26, 28, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 3, 5, 7, 11, 13, 11, 13, 15, 19, 21, 19, 21, 23, 27, 29, 27, 29]
def inputs : List Nat := [0xffffedb6cc63181c0,0x5ad6b6db5294a0e3f,0xad6b5b6da318c703f,0xf07c12493c1f07fc7,0xff8012493fe007ff8]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.and, [1,3]⟩,⟨.or, [2,5]⟩,⟨.and, [4,6]⟩,⟨.or, [0,8]⟩,⟨.and, [7,9]⟩], 10⟩

theorem exactSize : Exact (face 5 true) 6 := by
  have heq : face 5 true = fn 0xe8a8a8a8 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xe8a8a8a8 34 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X5B1
def sizes (p : Fin 6) (b : Bool) : ℕ :=
  if b then ![5, 5, 7, 7, 7, 6] p else ![3, 4, 3, 3, 5, 6] p
theorem profile (p : Fin 6) (b : Bool) : Exact (face p b) (sizes p b) := by
  fin_cases p <;> cases b
  · exact X0B0.exactSize
  · exact X0B1.exactSize
  · exact X1B0.exactSize
  · exact X1B1.exactSize
  · exact X2B0.exactSize
  · exact X2B1.exactSize
  · exact X3B0.exactSize
  · exact X3B1.exactSize
  · exact X4B0.exactSize
  · exact X4B1.exactSize
  · exact X5B0.exactSize
  · exact X5B1.exactSize
end Row15174Faces
#print axioms Row15174Faces.profile
