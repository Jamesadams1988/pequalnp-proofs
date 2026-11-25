import PEqualNP.Outside.L_meta_8657

/-!
Theorem `profile` gives exact unrestricted and monotone gate counts for all
twelve single-input restrictions of the six-input truth table in L-meta-15250.
For each coordinate, the remaining variables retain their original order.

The lower bounds instantiate Noptus's live-wire search from L-meta-8657.
Each sample pairs a zero row with a one row. The samples include all pairs of
maximal zeros and minimal ones and all sensitive, single-coordinate edges.
The theorem also supplies an explicit monotone circuit for each face.
-/

namespace Row15250Faces
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

def full (x : Fin 6 → Bool) := Nat.testBit (3936927872 * 2^32 + 3934830720)
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def face (p : Fin 6) (b : Bool) (x : Fin 5 → Bool) := full (p.insertNth b x)

def Exact (f : BFn 5) (size : ℕ) : Prop :=
  (∀ s, HasCircuitSize 5 f s → size ≤ s) ∧
    ∃ C : Circuit, Monotone2 C ∧ C.size = size ∧ ∀ x, C.eval (List.ofFn x) = f x

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace X0B0
def rows : List Nat := [27, 29, 30, 3, 5, 6, 11, 13, 14, 19, 21, 22, 27, 29, 30, 7, 7, 7, 7, 7, 7, 15, 15, 15, 23, 23, 23, 31, 31, 31]
def inputs : List Nat := [0x3fffb6db,0x3fffdb6d,0x3fffedb6,0x38e071c7,0x3f007e07]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.and, [2,5]⟩], 6⟩

theorem exactSize : Exact (face 0 false) 2 := by
  have heq : face 0 false = fn 0x80808080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0x80808080 15 1 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X0B0

namespace X0B1
def rows : List Nat := [10, 10, 10, 10, 21, 21, 21, 21, 22, 22, 22, 22, 24, 24, 24, 24, 1, 1, 2, 4, 5, 5, 6, 6, 8, 8, 10, 10, 17, 17, 18, 18, 20, 21, 21, 22, 22, 24, 24, 3, 9, 12, 26, 3, 9, 12, 26, 3, 9, 12, 26, 3, 9, 12, 26, 3, 9, 3, 12, 7, 13, 7, 14, 9, 12, 11, 14, 19, 25, 19, 26, 28, 23, 29, 23, 30, 25, 28]
def inputs : List Nat := [0x173abb999986303300f0,0xd6e6acccc98ccc40f0f,0x2f857c22221f00f80ff0,0x3ad7d57777600f00f00f,0x3ff80044447ff000fff0]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.or, [0,2]⟩,⟨.and, [1,4]⟩,⟨.or, [3,5]⟩,⟨.or, [6,7]⟩,⟨.and, [8,9]⟩], 10⟩

theorem exactSize : Exact (face 0 true) 6 := by
  have heq : face 0 true = fn 0xfe88fa88 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xfe88fa88 39 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X0B1

namespace X1B0
def rows : List Nat := [11, 11, 23, 23, 25, 25, 30, 30, 5, 7, 9, 11, 12, 14, 19, 21, 23, 25, 26, 28, 30, 13, 27, 13, 27, 13, 27, 13, 27, 13, 15, 13, 15, 13, 15, 27, 29, 31, 29, 27, 29, 31]
def inputs : List Nat := [0x3ffffe3cf3f,0x2ad55556acf,0x377eab9b3cc,0x3fffffe3cf3,0x3f8155fc0fc]
def circuit : Circuit := ⟨[⟨.and, [0,3]⟩,⟨.and, [1,4]⟩,⟨.or, [2,6]⟩,⟨.and, [5,7]⟩], 8⟩

theorem exactSize : Exact (face 1 false) 4 := by
  have heq : face 1 false = fn 0xa800a000 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xa800a000 21 3 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X1B0

namespace X1B1
def rows : List Nat := [21, 21, 21, 26, 26, 26, 28, 28, 28, 1, 1, 2, 2, 4, 5, 5, 8, 10, 10, 12, 12, 17, 17, 18, 18, 20, 21, 21, 24, 26, 26, 28, 28, 3, 6, 9, 3, 6, 9, 3, 6, 9, 3, 9, 3, 6, 6, 7, 13, 9, 11, 14, 13, 14, 19, 25, 19, 22, 22, 23, 29, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x179d79eda0c60c607,0x2cf6cf5b661861838,0x39e39e1258e18e1c7,0x3f0bf0a49f01f01f8,0x3ffc00001ffe001ff]
def circuit : Circuit := ⟨[⟨.or, [0,2]⟩,⟨.and, [0,3]⟩,⟨.and, [1,5]⟩,⟨.or, [6,7]⟩], 8⟩

theorem exactSize : Exact (face 1 true) 4 := by
  have heq : face 1 true = fn 0xeac8eac8 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeac8eac8 33 3 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X1B1

namespace X2B0
def rows : List Nat := [23, 23, 25, 25, 30, 30, 3, 5, 7, 9, 9, 10, 12, 14, 19, 21, 23, 25, 25, 26, 28, 30, 11, 13, 11, 13, 11, 13, 11, 13, 15, 11, 13, 11, 13, 15, 27, 29, 31, 27, 29, 27, 29, 31]
def inputs : List Nat := [0xfffffc7c7cf,0xadad5696973,0xd6d6ab1b1b3,0xffffffe3e3c,0xff0003fc03f]
def circuit : Circuit := ⟨[⟨.and, [0,3]⟩,⟨.or, [1,2]⟩,⟨.and, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 2 false) 3 := by
  have heq : face 2 false = fn 0xa800a800 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xa800a800 22 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X2B0

namespace X2B1
def rows : List Nat := [9, 9, 9, 9, 21, 21, 21, 21, 26, 26, 26, 26, 28, 28, 28, 28, 1, 2, 2, 4, 5, 5, 9, 10, 10, 12, 12, 17, 17, 18, 18, 20, 21, 21, 24, 26, 26, 28, 28, 3, 6, 13, 25, 3, 6, 13, 25, 3, 6, 13, 25, 3, 6, 13, 25, 3, 3, 6, 6, 7, 13, 11, 11, 14, 13, 14, 19, 25, 19, 22, 22, 23, 29, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x179d79eeee83187100ff,0x2cf6ef99999861860f00,0x39e39e3333638638f0f0,0x3f0bf066667c07c0ff0f,0x3ffc0044447ff800fff0]
def circuit : Circuit := ⟨[⟨.or, [0,2]⟩,⟨.and, [0,3]⟩,⟨.and, [1,5]⟩,⟨.or, [2,4]⟩,⟨.and, [6,8]⟩,⟨.or, [7,9]⟩], 10⟩

theorem exactSize : Exact (face 2 true) 6 := by
  have heq : face 2 true = fn 0xeac8e8c8 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeac8e8c8 39 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X2B1

namespace X3B0
def rows : List Nat := [13, 13, 13, 19, 19, 19, 21, 21, 21, 25, 25, 25, 30, 30, 30, 3, 3, 5, 6, 9, 10, 13, 14, 19, 19, 21, 22, 25, 26, 28, 30, 7, 11, 29, 7, 11, 29, 7, 11, 29, 7, 11, 29, 7, 11, 29, 7, 11, 7, 7, 11, 11, 15, 15, 23, 27, 23, 23, 27, 27, 29, 31]
def inputs : List Nat := [0x3fffffff8bab8fff,0x2fffdb6dd5d5f038,0x33736db6e66671c7,0x3cbcb6db78787e07,0x3fc024927f807ff8]
def circuit : Circuit := ⟨[⟨.and, [1,2]⟩,⟨.and, [2,4]⟩,⟨.or, [1,6]⟩,⟨.and, [0,7]⟩,⟨.or, [3,5]⟩,⟨.and, [8,9]⟩], 10⟩

theorem exactSize : Exact (face 3 false) 6 := by
  have heq : face 3 false = fn 0xa8808880 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xa8808880 31 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X3B0

namespace X3B1
def rows : List Nat := [19, 19, 21, 21, 26, 26, 28, 28, 1, 2, 3, 3, 4, 5, 5, 8, 10, 10, 12, 12, 17, 18, 19, 19, 20, 21, 21, 24, 26, 26, 28, 28, 6, 9, 6, 9, 6, 9, 6, 9, 9, 6, 7, 11, 6, 7, 13, 9, 11, 14, 13, 14, 25, 22, 23, 27, 22, 23, 29, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x5ed5edaa06d06d0f,0xb3eb3e5530e30e33,0xe76e7655c70c70cc,0xfc9fc9aaf80f80f0,0xfff00000fff000ff]
def circuit : Circuit := ⟨[⟨.and, [0,3]⟩,⟨.and, [1,2]⟩,⟨.or, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 3 true) 3 := by
  have heq : face 3 true = fn 0xeac0eac0 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeac0eac0 32 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X3B1

namespace X4B0
def rows : List Nat := [22, 22, 27, 27, 29, 29, 3, 5, 6, 6, 10, 11, 12, 13, 19, 21, 22, 22, 26, 27, 28, 29, 7, 14, 7, 14, 7, 14, 7, 7, 7, 14, 14, 15, 14, 15, 23, 23, 23, 30, 30, 31, 30, 31]
def inputs : List Nat := [0xa7a7568e8fc,0xfffffcf4f4f,0xffffff3b3b3,0xf8f8abc3c3c,0xff0003fc03f]
def circuit : Circuit := ⟨[⟨.or, [0,3]⟩,⟨.and, [1,2]⟩,⟨.and, [5,6]⟩], 7⟩

theorem exactSize : Exact (face 4 false) 3 := by
  have heq : face 4 false = fn 0xc080c080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xc080c080 22 2 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X4B0

namespace X4B1
def rows : List Nat := [5, 5, 5, 5, 17, 17, 17, 17, 22, 22, 22, 22, 26, 26, 26, 26, 28, 28, 28, 28, 1, 1, 2, 5, 5, 6, 6, 8, 10, 10, 12, 12, 17, 17, 18, 20, 22, 22, 24, 26, 26, 28, 28, 3, 9, 14, 21, 3, 9, 14, 21, 3, 9, 14, 21, 3, 9, 14, 21, 3, 9, 14, 21, 3, 9, 3, 7, 13, 7, 14, 9, 11, 14, 13, 14, 19, 25, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x16fadfddddd80301b000ff,0x2dadb6aaaaa9b43640ff00,0x39c73c66666638c78f0f0f,0x3f17e9333337c0f80ff000,0x3ff800444447ff000ffff0]
def circuit : Circuit := ⟨[⟨.and, [0,4]⟩,⟨.and, [1,3]⟩,⟨.or, [1,3]⟩,⟨.and, [0,7]⟩,⟨.or, [5,6]⟩,⟨.and, [2,9]⟩,⟨.or, [8,10]⟩], 11⟩

theorem exactSize : Exact (face 4 true) 7 := by
  have heq : face 4 true = fn 0xeaa8ea88 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeaa8ea88 43 6 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X4B1

namespace X5B0
def rows : List Nat := [11, 11, 11, 11, 13, 13, 13, 13, 21, 21, 21, 21, 22, 22, 22, 22, 26, 26, 26, 26, 28, 28, 28, 28, 3, 3, 5, 6, 6, 9, 10, 11, 11, 12, 13, 13, 17, 17, 18, 21, 21, 22, 22, 24, 26, 26, 28, 28, 7, 14, 19, 25, 7, 14, 19, 25, 7, 14, 19, 25, 7, 14, 19, 25, 7, 14, 19, 25, 7, 14, 19, 25, 7, 19, 7, 7, 14, 25, 14, 15, 27, 14, 15, 29, 19, 25, 19, 23, 29, 23, 30, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x5bfdafdddddd01bda7000fff,0xb6d7df7777773641db0ff00f,0xe78edd333333c78e1cf0fff0,0xfd2ff0aaaaaaf80fe0ff00ff,0xfff922ccccccfff000ffff00]
def circuit : Circuit := ⟨[⟨.and, [0,1]⟩,⟨.and, [0,4]⟩,⟨.and, [1,2]⟩,⟨.or, [3,5]⟩,⟨.or, [6,7]⟩,⟨.and, [8,9]⟩], 10⟩

theorem exactSize : Exact (face 5 false) 6 := by
  have heq : face 5 false = fn 0xea88c080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xea88c080 48 5 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X5B0

namespace X5B1
def rows : List Nat := [11, 11, 11, 11, 11, 13, 13, 13, 13, 13, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 3, 3, 5, 5, 6, 6, 9, 10, 11, 11, 12, 13, 13, 18, 20, 22, 22, 24, 26, 26, 28, 28, 7, 14, 19, 21, 25, 7, 14, 19, 21, 25, 7, 14, 19, 21, 25, 7, 14, 19, 21, 25, 7, 14, 19, 21, 25, 7, 14, 19, 21, 25, 7, 19, 7, 21, 7, 14, 25, 14, 15, 27, 14, 15, 29, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def inputs : List Nat := [0x5bed7fbdef7bd006d3c0007fff,0xb6bedce739ce7368ecc1ff801f,0xe776f56b5ad6bc770f3e0f83e0,0xfc7f825294a52f87f03ff003ff,0xffc92b9ce739cff8003ffffc00]
def circuit : Circuit := ⟨[⟨.and, [0,4]⟩,⟨.and, [1,2]⟩,⟨.or, [1,2]⟩,⟨.and, [0,7]⟩,⟨.or, [3,8]⟩,⟨.or, [5,6]⟩,⟨.and, [9,10]⟩], 11⟩

theorem exactSize : Exact (face 5 true) 7 := by
  have heq : face 5 true = fn 0xeaa8c080 := funext (by decide +kernel)
  rw [heq]
  refine ⟨lowerOfSamples 0xeaa8c080 52 6 rows inputs
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel), circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel
end X5B1
def sizes (p : Fin 6) (b : Bool) : ℕ :=
  if b then ![6, 4, 6, 3, 7, 7] p else ![2, 4, 3, 6, 3, 6] p
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
end Row15250Faces
#print axioms Row15250Faces.profile
