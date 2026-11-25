import HallLocal

noncomputable section
namespace Row169.ColumnRoot
open PEqualNP.ProofComplexity Row169.HallLocal
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V

private def c0 : C := {((1,0),true),((2,0),true),((3,0),true),((4,0),true)}
private def c1 : C := {((0,0),true),((2,0),true),((3,0),true),((4,0),true)}
private def c2 : C := {((0,0),true),((1,0),true),((3,0),true),((4,0),true)}
private def c3 : C := {((0,0),true),((1,0),true),((2,0),true),((4,0),true)}
private def c4 : C := {((0,0),true),((1,0),true),((2,0),true),((3,0),true)}
private def c5 : C := {((1,0),false),((0,0),false)}
private def c6 : C := {((2,0),false),((0,0),false)}
private def c7 : C := {((3,0),false),((0,0),false)}
private def c8 : C := {((4,0),false),((0,0),false)}
private def c9 : C := {((2,0),false),((1,0),false)}
private def c10 : C := {((3,0),false),((1,0),false)}
private def c11 : C := {((4,0),false),((1,0),false)}
private def c12 : C := {((3,0),false),((2,0),false)}
private def c13 : C := {((4,0),false),((2,0),false)}
private def c14 : C := {((4,0),false),((3,0),false)}
private def c15 : C := {((4,0),false),((1,0),true),((2,0),true),((3,0),true)}
private def c16 : C := {((4,0),false),((2,0),true),((3,0),true)}
private def c17 : C := {((4,0),false),((3,0),true)}
private def c18 : C := {((4,0),false)}
private def c19 : C := {((3,0),false),((1,0),true),((2,0),true),((4,0),true)}
private def c20 : C := {((3,0),false),((2,0),true),((4,0),true)}
private def c21 : C := {((3,0),false),((4,0),true)}
private def c22 : C := {((2,0),false),((1,0),true),((3,0),true),((4,0),true)}
private def c23 : C := {((2,0),false),((3,0),true),((4,0),true)}
private def c24 : C := {((1,0),false),((2,0),true),((3,0),true),((4,0),true)}
private def c25 : C := {((2,0),true),((3,0),true),((4,0),true)}
private def c26 : C := {((3,0),true),((4,0),true)}
private def c27 : C := {((4,0),true)}
private def c28 : C := ∅

private def sourceList : List C := [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14]
def premises : Finset C := sourceList.toFinset
private def b0 := premises.toList
private theorem d0 : Joined premises 0 b0 := .start

private def b1 := c15 :: b0
private theorem d1 : Joined premises 1 b1 := Joined.step d0 (A:=c4) (B:=c8)
  (Finset.mem_toList.mpr (by decide +kernel : c4 ∈ premises)) (Finset.mem_toList.mpr (by decide +kernel : c8 ∈ premises)) ⟨(0,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b2 := c16 :: b1
private theorem d2 : Joined premises 2 b2 := Joined.step d1 (A:=c15) (B:=c11)
  (List.Mem.head _) (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c11 ∈ premises))) ⟨(1,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b3 := c17 :: b2
private theorem d3 : Joined premises 3 b3 := Joined.step d2 (A:=c16) (B:=c13)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c13 ∈ premises)))) ⟨(2,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b4 := c18 :: b3
private theorem d4 : Joined premises 4 b4 := Joined.step d3 (A:=c17) (B:=c14)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c14 ∈ premises))))) ⟨(3,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b5 := c19 :: b4
private theorem d5 : Joined premises 5 b5 := Joined.step d4 (A:=c3) (B:=c7)
  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c3 ∈ premises)))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c7 ∈ premises)))))) ⟨(0,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b6 := c20 :: b5
private theorem d6 : Joined premises 6 b6 := Joined.step d5 (A:=c19) (B:=c10)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c10 ∈ premises))))))) ⟨(1,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b7 := c21 :: b6
private theorem d7 : Joined premises 7 b7 := Joined.step d6 (A:=c20) (B:=c12)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c12 ∈ premises)))))))) ⟨(2,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b8 := c22 :: b7
private theorem d8 : Joined premises 8 b8 := Joined.step d7 (A:=c2) (B:=c6)
  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c2 ∈ premises))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c6 ∈ premises))))))))) ⟨(0,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b9 := c23 :: b8
private theorem d9 : Joined premises 9 b9 := Joined.step d8 (A:=c22) (B:=c9)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c9 ∈ premises)))))))))) ⟨(1,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b10 := c24 :: b9
private theorem d10 : Joined premises 10 b10 := Joined.step d9 (A:=c1) (B:=c5)
  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c1 ∈ premises))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c5 ∈ premises))))))))))) ⟨(0,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b11 := c25 :: b10
private theorem d11 : Joined premises 11 b11 := Joined.step d10 (A:=c0) (B:=c24)
  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (Finset.mem_toList.mpr (by decide +kernel : c0 ∈ premises)))))))))))) (List.Mem.head _) ⟨(1,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b12 := c26 :: b11
private theorem d12 : Joined premises 12 b12 := Joined.step d11 (A:=c25) (B:=c23)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ⟨(2,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b13 := c27 :: b12
private theorem d13 : Joined premises 13 b13 := Joined.step d12 (A:=c26) (B:=c21)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨(3,0), by decide +kernel, by decide +kernel, by decide +kernel⟩
private def b14 := c28 :: b13
private theorem d14 : Joined premises 14 b14 := Joined.step d13 (A:=c27) (B:=c18)
  (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) ⟨(4,0), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem attained : ∃ π, Joined premises 14 π ∧ (∅ : C) ∈ π :=
  ⟨b14,d14,List.Mem.head _⟩

private instance (a : V → Bool) (c : C) : Decidable (ClauseSat a c) := by
  unfold ClauseSat
  infer_instance

private def critical (c : C) (v : V) : Bool :=
  v.2 == 0 && (if (∃ z ∈ c, z.2 = false) then decide ((v,false) ∈ c) else decide ((v,true) ∉ c))

theorem necessary {n π} (built : Joined premises n π) (ht : (∅ : C) ∈ π) : 14 ≤ n := by
  have pass : (sourceList.all fun c => sourceList.all fun d =>
      decide (c = d) || decide (ClauseSat (critical c) d)) = true := by decide +kernel
  have unique : ∀ c ∈ premises, ∀ d ∈ premises, ¬ ClauseSat (critical c) d → c = d := by
    intro c hc d hd bad
    have row := List.all_eq_true.mp pass c (List.mem_toFinset.mp hc)
    have item := List.all_eq_true.mp row d (List.mem_toFinset.mp hd)
    simpa [bad] using item
  have bad : ∀ c ∈ premises, ¬ ClauseSat (critical c) (∅ : C) := by
    intro c hc
    simp [ClauseSat]
  have card : premises.card = 15 := by decide +kernel
  have := joinsNeeded critical unique bad built ht
  omega

#print axioms attained
#print axioms necessary
end Row169.ColumnRoot
