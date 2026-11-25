import PEqualNP.Defs

namespace Row133.Parity
open PEqualNP.ProofComplexity
private abbrev V := Fin 5 × Fin 2
private abbrev LC := LinClause V
private abbrev F := ((fun C => linOfClause C) '' BPHP 5 2)

private def inputClause (i j : Fin 5) (h : Nat) : Clause V :=
  Finset.univ.image (fun b : Fin 2 => ((i,b), !h.testBit b.val)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j,b), !h.testBit b.val))
private theorem inputMem (i j : Fin 5) (h : Nat) (hd : i ≠ j) : linOfClause (inputClause i j h) ∈ F :=
  ⟨inputClause i j h, ⟨i,j,fun b => h.testBit b.val,hd,rfl⟩,rfl⟩
private theorem lineAt (l : List LC) (k : ℕ) (bound : k < l.length) : l[k] ∈ l := List.getElem_mem bound

private instance (a : V → Bool) (q : LinEq V) : Decidable (LinEqSat a q) := by
  unfold LinEqSat
  infer_instance
private instance (a : V → Bool) (C : LC) : Decidable (LinClauseSat a C) := by
  unfold LinClauseSat
  infer_instance

private def localAssignment (vars : List V) (bits : BitVec vars.length) (v : V) : Bool :=
  bits.getLsbD (vars.idxOf v)

private theorem localAgrees (vars : List V) (a : V → Bool) :
    ∃ w : BitVec vars.length, ∀ v ∈ vars, localAssignment vars w v = a v := by
  let w := (BitVec.ofBoolListLE (vars.map a)).cast (by simp : (vars.map a).length = vars.length)
  refine ⟨w,?_⟩
  intro v hv
  have i := List.idxOf_lt_length_iff.mpr hv
  have e := List.getElem_idxOf (xs := vars) i
  simp [localAssignment,w,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i,e]

private theorem satCongr (vars : List V) (a b : V → Bool) (h : ∀ v ∈ vars, a v = b v)
    (C : LC) (support : ∀ q ∈ C, q.1 ⊆ vars.toFinset) : LinClauseSat a C ↔ LinClauseSat b C := by
  have eq (q : LinEq V) (hq : q ∈ C) : LinEqSat a q ↔ LinEqSat b q := by
    have same : q.1.filter (fun v => a v = true) = q.1.filter (fun v => b v = true) := by
      ext v
      by_cases hv : v ∈ q.1
      · have hv' := h v (List.mem_toFinset.mp (support q hq hv))
        simp [hv,hv']
      · simp [hv]
    simp only [LinEqSat,same]
  constructor
  · rintro ⟨q,hq,holds⟩
    exact ⟨q,hq,(eq q hq).mp holds⟩
  · rintro ⟨q,hq,holds⟩
    exact ⟨q,hq,(eq q hq).mpr holds⟩

private theorem checkedWeak (vars : List V) (C D : LC)
    (hs : ∀ q ∈ C, q.1 ⊆ vars.toFinset) (ht : ∀ q ∈ D, q.1 ⊆ vars.toFinset)
    (valid : ∀ bits : BitVec vars.length,
      LinClauseSat (localAssignment vars bits) C → LinClauseSat (localAssignment vars bits) D) :
    ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  intro a ha
  obtain ⟨w,hw⟩ := localAgrees vars a
  exact (satCongr vars _ a hw D ht).mp (valid w ((satCongr vars _ a hw C hs).mpr ha))

private def l0 : LC := linOfClause (inputClause 0 1 0)
private def p0 : List LC := l0 :: []
private theorem d0 : IsLinDerivation F p0 :=
  IsLinDerivation.ax IsLinDerivation.nil (inputMem 0 1 0 (by decide))

private def l1 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p1 : List LC := l1 :: p0
private theorem d1 : IsLinDerivation F p1 :=
  IsLinDerivation.weak (C := l0) d0
    (lineAt p0 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(1,0),(1,1)] l0 l1
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l2 : LC := linOfClause (inputClause 0 1 1)
private def p2 : List LC := l2 :: p1
private theorem d2 : IsLinDerivation F p2 :=
  IsLinDerivation.ax d1 (inputMem 0 1 1 (by decide))

private def l3 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p3 : List LC := l3 :: p2
private theorem d3 : IsLinDerivation F p3 :=
  IsLinDerivation.weak (C := l2) d2
    (lineAt p2 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(1,0),(1,1)] l2 l3
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l4 : LC := linOfClause (inputClause 0 1 2)
private def p4 : List LC := l4 :: p3
private theorem d4 : IsLinDerivation F p4 :=
  IsLinDerivation.ax d3 (inputMem 0 1 2 (by decide))

private def l5 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p5 : List LC := l5 :: p4
private theorem d5 : IsLinDerivation F p5 :=
  IsLinDerivation.weak (C := l4) d4
    (lineAt p4 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(1,0),(1,1)] l4 l5
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l6 : LC := linOfClause (inputClause 0 1 3)
private def p6 : List LC := l6 :: p5
private theorem d6 : IsLinDerivation F p6 :=
  IsLinDerivation.ax d5 (inputMem 0 1 3 (by decide))

private def l7 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p7 : List LC := l7 :: p6
private theorem d7 : IsLinDerivation F p7 :=
  IsLinDerivation.weak (C := l6) d6
    (lineAt p6 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(1,0),(1,1)] l6 l7
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l8 : LC := {(({(0,1)} : Finset V),true),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p8 : List LC := l8 :: p7
private theorem d8 : IsLinDerivation F p8 :=
  IsLinDerivation.res (C := l3) (D := l1) d7
    (lineAt p7 4 (by decide +kernel)) (lineAt p7 6 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l9 : LC := {(({(0,1)} : Finset V),false),(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p9 : List LC := l9 :: p8
private theorem d9 : IsLinDerivation F p9 :=
  IsLinDerivation.res (C := l7) (D := l5) d8
    (lineAt p8 1 (by decide +kernel)) (lineAt p8 3 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l10 : LC := {(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),true)}
private def p10 : List LC := l10 :: p9
private theorem d10 : IsLinDerivation F p10 :=
  IsLinDerivation.res (C := l9) (D := l8) d9
    (lineAt p9 0 (by decide +kernel)) (lineAt p9 1 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l11 : LC := linOfClause (inputClause 0 2 0)
private def p11 : List LC := l11 :: p10
private theorem d11 : IsLinDerivation F p11 :=
  IsLinDerivation.ax d10 (inputMem 0 2 0 (by decide))

private def l12 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p12 : List LC := l12 :: p11
private theorem d12 : IsLinDerivation F p12 :=
  IsLinDerivation.weak (C := l11) d11
    (lineAt p11 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(2,0),(2,1)] l11 l12
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l13 : LC := linOfClause (inputClause 0 2 1)
private def p13 : List LC := l13 :: p12
private theorem d13 : IsLinDerivation F p13 :=
  IsLinDerivation.ax d12 (inputMem 0 2 1 (by decide))

private def l14 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p14 : List LC := l14 :: p13
private theorem d14 : IsLinDerivation F p14 :=
  IsLinDerivation.weak (C := l13) d13
    (lineAt p13 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(2,0),(2,1)] l13 l14
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l15 : LC := linOfClause (inputClause 0 2 2)
private def p15 : List LC := l15 :: p14
private theorem d15 : IsLinDerivation F p15 :=
  IsLinDerivation.ax d14 (inputMem 0 2 2 (by decide))

private def l16 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p16 : List LC := l16 :: p15
private theorem d16 : IsLinDerivation F p16 :=
  IsLinDerivation.weak (C := l15) d15
    (lineAt p15 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(2,0),(2,1)] l15 l16
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l17 : LC := linOfClause (inputClause 0 2 3)
private def p17 : List LC := l17 :: p16
private theorem d17 : IsLinDerivation F p17 :=
  IsLinDerivation.ax d16 (inputMem 0 2 3 (by decide))

private def l18 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p18 : List LC := l18 :: p17
private theorem d18 : IsLinDerivation F p18 :=
  IsLinDerivation.weak (C := l17) d17
    (lineAt p17 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(2,0),(2,1)] l17 l18
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l19 : LC := {(({(0,1)} : Finset V),true),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p19 : List LC := l19 :: p18
private theorem d19 : IsLinDerivation F p19 :=
  IsLinDerivation.res (C := l14) (D := l12) d18
    (lineAt p18 4 (by decide +kernel)) (lineAt p18 6 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l20 : LC := {(({(0,1)} : Finset V),false),(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p20 : List LC := l20 :: p19
private theorem d20 : IsLinDerivation F p20 :=
  IsLinDerivation.res (C := l18) (D := l16) d19
    (lineAt p19 1 (by decide +kernel)) (lineAt p19 3 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l21 : LC := {(({(0,0),(2,0)} : Finset V),true),(({(0,1),(2,1)} : Finset V),true)}
private def p21 : List LC := l21 :: p20
private theorem d21 : IsLinDerivation F p21 :=
  IsLinDerivation.res (C := l20) (D := l19) d20
    (lineAt p20 0 (by decide +kernel)) (lineAt p20 1 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l22 : LC := linOfClause (inputClause 0 3 0)
private def p22 : List LC := l22 :: p21
private theorem d22 : IsLinDerivation F p22 :=
  IsLinDerivation.ax d21 (inputMem 0 3 0 (by decide))

private def l23 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p23 : List LC := l23 :: p22
private theorem d23 : IsLinDerivation F p23 :=
  IsLinDerivation.weak (C := l22) d22
    (lineAt p22 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(3,0),(3,1)] l22 l23
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l24 : LC := linOfClause (inputClause 0 3 1)
private def p24 : List LC := l24 :: p23
private theorem d24 : IsLinDerivation F p24 :=
  IsLinDerivation.ax d23 (inputMem 0 3 1 (by decide))

private def l25 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p25 : List LC := l25 :: p24
private theorem d25 : IsLinDerivation F p25 :=
  IsLinDerivation.weak (C := l24) d24
    (lineAt p24 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(3,0),(3,1)] l24 l25
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l26 : LC := linOfClause (inputClause 0 3 2)
private def p26 : List LC := l26 :: p25
private theorem d26 : IsLinDerivation F p26 :=
  IsLinDerivation.ax d25 (inputMem 0 3 2 (by decide))

private def l27 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p27 : List LC := l27 :: p26
private theorem d27 : IsLinDerivation F p27 :=
  IsLinDerivation.weak (C := l26) d26
    (lineAt p26 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(3,0),(3,1)] l26 l27
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l28 : LC := linOfClause (inputClause 0 3 3)
private def p28 : List LC := l28 :: p27
private theorem d28 : IsLinDerivation F p28 :=
  IsLinDerivation.ax d27 (inputMem 0 3 3 (by decide))

private def l29 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p29 : List LC := l29 :: p28
private theorem d29 : IsLinDerivation F p29 :=
  IsLinDerivation.weak (C := l28) d28
    (lineAt p28 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(3,0),(3,1)] l28 l29
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l30 : LC := {(({(0,1)} : Finset V),true),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p30 : List LC := l30 :: p29
private theorem d30 : IsLinDerivation F p30 :=
  IsLinDerivation.res (C := l25) (D := l23) d29
    (lineAt p29 4 (by decide +kernel)) (lineAt p29 6 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l31 : LC := {(({(0,1)} : Finset V),false),(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p31 : List LC := l31 :: p30
private theorem d31 : IsLinDerivation F p31 :=
  IsLinDerivation.res (C := l29) (D := l27) d30
    (lineAt p30 1 (by decide +kernel)) (lineAt p30 3 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l32 : LC := {(({(0,0),(3,0)} : Finset V),true),(({(0,1),(3,1)} : Finset V),true)}
private def p32 : List LC := l32 :: p31
private theorem d32 : IsLinDerivation F p32 :=
  IsLinDerivation.res (C := l31) (D := l30) d31
    (lineAt p31 0 (by decide +kernel)) (lineAt p31 1 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l33 : LC := linOfClause (inputClause 0 4 0)
private def p33 : List LC := l33 :: p32
private theorem d33 : IsLinDerivation F p33 :=
  IsLinDerivation.ax d32 (inputMem 0 4 0 (by decide))

private def l34 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p34 : List LC := l34 :: p33
private theorem d34 : IsLinDerivation F p34 :=
  IsLinDerivation.weak (C := l33) d33
    (lineAt p33 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(4,0),(4,1)] l33 l34
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l35 : LC := linOfClause (inputClause 0 4 1)
private def p35 : List LC := l35 :: p34
private theorem d35 : IsLinDerivation F p35 :=
  IsLinDerivation.ax d34 (inputMem 0 4 1 (by decide))

private def l36 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p36 : List LC := l36 :: p35
private theorem d36 : IsLinDerivation F p36 :=
  IsLinDerivation.weak (C := l35) d35
    (lineAt p35 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(4,0),(4,1)] l35 l36
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l37 : LC := linOfClause (inputClause 0 4 2)
private def p37 : List LC := l37 :: p36
private theorem d37 : IsLinDerivation F p37 :=
  IsLinDerivation.ax d36 (inputMem 0 4 2 (by decide))

private def l38 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p38 : List LC := l38 :: p37
private theorem d38 : IsLinDerivation F p38 :=
  IsLinDerivation.weak (C := l37) d37
    (lineAt p37 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(4,0),(4,1)] l37 l38
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l39 : LC := linOfClause (inputClause 0 4 3)
private def p39 : List LC := l39 :: p38
private theorem d39 : IsLinDerivation F p39 :=
  IsLinDerivation.ax d38 (inputMem 0 4 3 (by decide))

private def l40 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p40 : List LC := l40 :: p39
private theorem d40 : IsLinDerivation F p40 :=
  IsLinDerivation.weak (C := l39) d39
    (lineAt p39 0 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(4,0),(4,1)] l39 l40
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l41 : LC := {(({(0,1)} : Finset V),true),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p41 : List LC := l41 :: p40
private theorem d41 : IsLinDerivation F p41 :=
  IsLinDerivation.res (C := l36) (D := l34) d40
    (lineAt p40 4 (by decide +kernel)) (lineAt p40 6 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l42 : LC := {(({(0,1)} : Finset V),false),(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p42 : List LC := l42 :: p41
private theorem d42 : IsLinDerivation F p42 :=
  IsLinDerivation.res (C := l40) (D := l38) d41
    (lineAt p41 1 (by decide +kernel)) (lineAt p41 3 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l43 : LC := {(({(0,0),(4,0)} : Finset V),true),(({(0,1),(4,1)} : Finset V),true)}
private def p43 : List LC := l43 :: p42
private theorem d43 : IsLinDerivation F p43 :=
  IsLinDerivation.res (C := l42) (D := l41) d42
    (lineAt p42 0 (by decide +kernel)) (lineAt p42 1 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l44 : LC := linOfClause (inputClause 1 2 0)
private def p44 : List LC := l44 :: p43
private theorem d44 : IsLinDerivation F p44 :=
  IsLinDerivation.ax d43 (inputMem 1 2 0 (by decide))

private def l45 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p45 : List LC := l45 :: p44
private theorem d45 : IsLinDerivation F p45 :=
  IsLinDerivation.weak (C := l44) d44
    (lineAt p44 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(2,0),(2,1)] l44 l45
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l46 : LC := linOfClause (inputClause 1 2 1)
private def p46 : List LC := l46 :: p45
private theorem d46 : IsLinDerivation F p46 :=
  IsLinDerivation.ax d45 (inputMem 1 2 1 (by decide))

private def l47 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p47 : List LC := l47 :: p46
private theorem d47 : IsLinDerivation F p47 :=
  IsLinDerivation.weak (C := l46) d46
    (lineAt p46 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(2,0),(2,1)] l46 l47
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l48 : LC := linOfClause (inputClause 1 2 2)
private def p48 : List LC := l48 :: p47
private theorem d48 : IsLinDerivation F p48 :=
  IsLinDerivation.ax d47 (inputMem 1 2 2 (by decide))

private def l49 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p49 : List LC := l49 :: p48
private theorem d49 : IsLinDerivation F p49 :=
  IsLinDerivation.weak (C := l48) d48
    (lineAt p48 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(2,0),(2,1)] l48 l49
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l50 : LC := linOfClause (inputClause 1 2 3)
private def p50 : List LC := l50 :: p49
private theorem d50 : IsLinDerivation F p50 :=
  IsLinDerivation.ax d49 (inputMem 1 2 3 (by decide))

private def l51 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p51 : List LC := l51 :: p50
private theorem d51 : IsLinDerivation F p51 :=
  IsLinDerivation.weak (C := l50) d50
    (lineAt p50 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(2,0),(2,1)] l50 l51
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l52 : LC := {(({(1,1)} : Finset V),true),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p52 : List LC := l52 :: p51
private theorem d52 : IsLinDerivation F p52 :=
  IsLinDerivation.res (C := l47) (D := l45) d51
    (lineAt p51 4 (by decide +kernel)) (lineAt p51 6 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l53 : LC := {(({(1,1)} : Finset V),false),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p53 : List LC := l53 :: p52
private theorem d53 : IsLinDerivation F p53 :=
  IsLinDerivation.res (C := l51) (D := l49) d52
    (lineAt p52 1 (by decide +kernel)) (lineAt p52 3 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l54 : LC := {(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),true)}
private def p54 : List LC := l54 :: p53
private theorem d54 : IsLinDerivation F p54 :=
  IsLinDerivation.res (C := l53) (D := l52) d53
    (lineAt p53 0 (by decide +kernel)) (lineAt p53 1 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l55 : LC := linOfClause (inputClause 1 3 0)
private def p55 : List LC := l55 :: p54
private theorem d55 : IsLinDerivation F p55 :=
  IsLinDerivation.ax d54 (inputMem 1 3 0 (by decide))

private def l56 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p56 : List LC := l56 :: p55
private theorem d56 : IsLinDerivation F p56 :=
  IsLinDerivation.weak (C := l55) d55
    (lineAt p55 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(3,0),(3,1)] l55 l56
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l57 : LC := linOfClause (inputClause 1 3 1)
private def p57 : List LC := l57 :: p56
private theorem d57 : IsLinDerivation F p57 :=
  IsLinDerivation.ax d56 (inputMem 1 3 1 (by decide))

private def l58 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p58 : List LC := l58 :: p57
private theorem d58 : IsLinDerivation F p58 :=
  IsLinDerivation.weak (C := l57) d57
    (lineAt p57 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(3,0),(3,1)] l57 l58
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l59 : LC := linOfClause (inputClause 1 3 2)
private def p59 : List LC := l59 :: p58
private theorem d59 : IsLinDerivation F p59 :=
  IsLinDerivation.ax d58 (inputMem 1 3 2 (by decide))

private def l60 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p60 : List LC := l60 :: p59
private theorem d60 : IsLinDerivation F p60 :=
  IsLinDerivation.weak (C := l59) d59
    (lineAt p59 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(3,0),(3,1)] l59 l60
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l61 : LC := linOfClause (inputClause 1 3 3)
private def p61 : List LC := l61 :: p60
private theorem d61 : IsLinDerivation F p61 :=
  IsLinDerivation.ax d60 (inputMem 1 3 3 (by decide))

private def l62 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p62 : List LC := l62 :: p61
private theorem d62 : IsLinDerivation F p62 :=
  IsLinDerivation.weak (C := l61) d61
    (lineAt p61 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(3,0),(3,1)] l61 l62
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l63 : LC := {(({(1,1)} : Finset V),true),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p63 : List LC := l63 :: p62
private theorem d63 : IsLinDerivation F p63 :=
  IsLinDerivation.res (C := l58) (D := l56) d62
    (lineAt p62 4 (by decide +kernel)) (lineAt p62 6 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l64 : LC := {(({(1,1)} : Finset V),false),(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p64 : List LC := l64 :: p63
private theorem d64 : IsLinDerivation F p64 :=
  IsLinDerivation.res (C := l62) (D := l60) d63
    (lineAt p63 1 (by decide +kernel)) (lineAt p63 3 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l65 : LC := {(({(1,0),(3,0)} : Finset V),true),(({(1,1),(3,1)} : Finset V),true)}
private def p65 : List LC := l65 :: p64
private theorem d65 : IsLinDerivation F p65 :=
  IsLinDerivation.res (C := l64) (D := l63) d64
    (lineAt p64 0 (by decide +kernel)) (lineAt p64 1 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l66 : LC := linOfClause (inputClause 1 4 0)
private def p66 : List LC := l66 :: p65
private theorem d66 : IsLinDerivation F p66 :=
  IsLinDerivation.ax d65 (inputMem 1 4 0 (by decide))

private def l67 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p67 : List LC := l67 :: p66
private theorem d67 : IsLinDerivation F p67 :=
  IsLinDerivation.weak (C := l66) d66
    (lineAt p66 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(4,0),(4,1)] l66 l67
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l68 : LC := linOfClause (inputClause 1 4 1)
private def p68 : List LC := l68 :: p67
private theorem d68 : IsLinDerivation F p68 :=
  IsLinDerivation.ax d67 (inputMem 1 4 1 (by decide))

private def l69 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p69 : List LC := l69 :: p68
private theorem d69 : IsLinDerivation F p69 :=
  IsLinDerivation.weak (C := l68) d68
    (lineAt p68 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(4,0),(4,1)] l68 l69
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l70 : LC := linOfClause (inputClause 1 4 2)
private def p70 : List LC := l70 :: p69
private theorem d70 : IsLinDerivation F p70 :=
  IsLinDerivation.ax d69 (inputMem 1 4 2 (by decide))

private def l71 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p71 : List LC := l71 :: p70
private theorem d71 : IsLinDerivation F p71 :=
  IsLinDerivation.weak (C := l70) d70
    (lineAt p70 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(4,0),(4,1)] l70 l71
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l72 : LC := linOfClause (inputClause 1 4 3)
private def p72 : List LC := l72 :: p71
private theorem d72 : IsLinDerivation F p72 :=
  IsLinDerivation.ax d71 (inputMem 1 4 3 (by decide))

private def l73 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p73 : List LC := l73 :: p72
private theorem d73 : IsLinDerivation F p73 :=
  IsLinDerivation.weak (C := l72) d72
    (lineAt p72 0 (by decide +kernel)) (checkedWeak [(1,0),(1,1),(4,0),(4,1)] l72 l73
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l74 : LC := {(({(1,1)} : Finset V),true),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p74 : List LC := l74 :: p73
private theorem d74 : IsLinDerivation F p74 :=
  IsLinDerivation.res (C := l69) (D := l67) d73
    (lineAt p73 4 (by decide +kernel)) (lineAt p73 6 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l75 : LC := {(({(1,1)} : Finset V),false),(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p75 : List LC := l75 :: p74
private theorem d75 : IsLinDerivation F p75 :=
  IsLinDerivation.res (C := l73) (D := l71) d74
    (lineAt p74 1 (by decide +kernel)) (lineAt p74 3 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l76 : LC := {(({(1,0),(4,0)} : Finset V),true),(({(1,1),(4,1)} : Finset V),true)}
private def p76 : List LC := l76 :: p75
private theorem d76 : IsLinDerivation F p76 :=
  IsLinDerivation.res (C := l75) (D := l74) d75
    (lineAt p75 0 (by decide +kernel)) (lineAt p75 1 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l77 : LC := linOfClause (inputClause 2 3 0)
private def p77 : List LC := l77 :: p76
private theorem d77 : IsLinDerivation F p77 :=
  IsLinDerivation.ax d76 (inputMem 2 3 0 (by decide))

private def l78 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p78 : List LC := l78 :: p77
private theorem d78 : IsLinDerivation F p78 :=
  IsLinDerivation.weak (C := l77) d77
    (lineAt p77 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(3,0),(3,1)] l77 l78
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l79 : LC := linOfClause (inputClause 2 3 1)
private def p79 : List LC := l79 :: p78
private theorem d79 : IsLinDerivation F p79 :=
  IsLinDerivation.ax d78 (inputMem 2 3 1 (by decide))

private def l80 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p80 : List LC := l80 :: p79
private theorem d80 : IsLinDerivation F p80 :=
  IsLinDerivation.weak (C := l79) d79
    (lineAt p79 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(3,0),(3,1)] l79 l80
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l81 : LC := linOfClause (inputClause 2 3 2)
private def p81 : List LC := l81 :: p80
private theorem d81 : IsLinDerivation F p81 :=
  IsLinDerivation.ax d80 (inputMem 2 3 2 (by decide))

private def l82 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p82 : List LC := l82 :: p81
private theorem d82 : IsLinDerivation F p82 :=
  IsLinDerivation.weak (C := l81) d81
    (lineAt p81 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(3,0),(3,1)] l81 l82
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l83 : LC := linOfClause (inputClause 2 3 3)
private def p83 : List LC := l83 :: p82
private theorem d83 : IsLinDerivation F p83 :=
  IsLinDerivation.ax d82 (inputMem 2 3 3 (by decide))

private def l84 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p84 : List LC := l84 :: p83
private theorem d84 : IsLinDerivation F p84 :=
  IsLinDerivation.weak (C := l83) d83
    (lineAt p83 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(3,0),(3,1)] l83 l84
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l85 : LC := {(({(2,1)} : Finset V),true),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p85 : List LC := l85 :: p84
private theorem d85 : IsLinDerivation F p85 :=
  IsLinDerivation.res (C := l80) (D := l78) d84
    (lineAt p84 4 (by decide +kernel)) (lineAt p84 6 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l86 : LC := {(({(2,1)} : Finset V),false),(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p86 : List LC := l86 :: p85
private theorem d86 : IsLinDerivation F p86 :=
  IsLinDerivation.res (C := l84) (D := l82) d85
    (lineAt p85 1 (by decide +kernel)) (lineAt p85 3 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l87 : LC := {(({(2,0),(3,0)} : Finset V),true),(({(2,1),(3,1)} : Finset V),true)}
private def p87 : List LC := l87 :: p86
private theorem d87 : IsLinDerivation F p87 :=
  IsLinDerivation.res (C := l86) (D := l85) d86
    (lineAt p86 0 (by decide +kernel)) (lineAt p86 1 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l88 : LC := linOfClause (inputClause 2 4 0)
private def p88 : List LC := l88 :: p87
private theorem d88 : IsLinDerivation F p88 :=
  IsLinDerivation.ax d87 (inputMem 2 4 0 (by decide))

private def l89 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p89 : List LC := l89 :: p88
private theorem d89 : IsLinDerivation F p89 :=
  IsLinDerivation.weak (C := l88) d88
    (lineAt p88 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(4,0),(4,1)] l88 l89
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l90 : LC := linOfClause (inputClause 2 4 1)
private def p90 : List LC := l90 :: p89
private theorem d90 : IsLinDerivation F p90 :=
  IsLinDerivation.ax d89 (inputMem 2 4 1 (by decide))

private def l91 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p91 : List LC := l91 :: p90
private theorem d91 : IsLinDerivation F p91 :=
  IsLinDerivation.weak (C := l90) d90
    (lineAt p90 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(4,0),(4,1)] l90 l91
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l92 : LC := linOfClause (inputClause 2 4 2)
private def p92 : List LC := l92 :: p91
private theorem d92 : IsLinDerivation F p92 :=
  IsLinDerivation.ax d91 (inputMem 2 4 2 (by decide))

private def l93 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p93 : List LC := l93 :: p92
private theorem d93 : IsLinDerivation F p93 :=
  IsLinDerivation.weak (C := l92) d92
    (lineAt p92 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(4,0),(4,1)] l92 l93
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l94 : LC := linOfClause (inputClause 2 4 3)
private def p94 : List LC := l94 :: p93
private theorem d94 : IsLinDerivation F p94 :=
  IsLinDerivation.ax d93 (inputMem 2 4 3 (by decide))

private def l95 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p95 : List LC := l95 :: p94
private theorem d95 : IsLinDerivation F p95 :=
  IsLinDerivation.weak (C := l94) d94
    (lineAt p94 0 (by decide +kernel)) (checkedWeak [(2,0),(2,1),(4,0),(4,1)] l94 l95
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l96 : LC := {(({(2,1)} : Finset V),true),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p96 : List LC := l96 :: p95
private theorem d96 : IsLinDerivation F p96 :=
  IsLinDerivation.res (C := l91) (D := l89) d95
    (lineAt p95 4 (by decide +kernel)) (lineAt p95 6 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l97 : LC := {(({(2,1)} : Finset V),false),(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p97 : List LC := l97 :: p96
private theorem d97 : IsLinDerivation F p97 :=
  IsLinDerivation.res (C := l95) (D := l93) d96
    (lineAt p96 1 (by decide +kernel)) (lineAt p96 3 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l98 : LC := {(({(2,0),(4,0)} : Finset V),true),(({(2,1),(4,1)} : Finset V),true)}
private def p98 : List LC := l98 :: p97
private theorem d98 : IsLinDerivation F p98 :=
  IsLinDerivation.res (C := l97) (D := l96) d97
    (lineAt p97 0 (by decide +kernel)) (lineAt p97 1 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l99 : LC := linOfClause (inputClause 3 4 0)
private def p99 : List LC := l99 :: p98
private theorem d99 : IsLinDerivation F p99 :=
  IsLinDerivation.ax d98 (inputMem 3 4 0 (by decide))

private def l100 : LC := {(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p100 : List LC := l100 :: p99
private theorem d100 : IsLinDerivation F p100 :=
  IsLinDerivation.weak (C := l99) d99
    (lineAt p99 0 (by decide +kernel)) (checkedWeak [(3,0),(3,1),(4,0),(4,1)] l99 l100
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l101 : LC := linOfClause (inputClause 3 4 1)
private def p101 : List LC := l101 :: p100
private theorem d101 : IsLinDerivation F p101 :=
  IsLinDerivation.ax d100 (inputMem 3 4 1 (by decide))

private def l102 : LC := {(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p102 : List LC := l102 :: p101
private theorem d102 : IsLinDerivation F p102 :=
  IsLinDerivation.weak (C := l101) d101
    (lineAt p101 0 (by decide +kernel)) (checkedWeak [(3,0),(3,1),(4,0),(4,1)] l101 l102
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l103 : LC := linOfClause (inputClause 3 4 2)
private def p103 : List LC := l103 :: p102
private theorem d103 : IsLinDerivation F p103 :=
  IsLinDerivation.ax d102 (inputMem 3 4 2 (by decide))

private def l104 : LC := {(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p104 : List LC := l104 :: p103
private theorem d104 : IsLinDerivation F p104 :=
  IsLinDerivation.weak (C := l103) d103
    (lineAt p103 0 (by decide +kernel)) (checkedWeak [(3,0),(3,1),(4,0),(4,1)] l103 l104
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l105 : LC := linOfClause (inputClause 3 4 3)
private def p105 : List LC := l105 :: p104
private theorem d105 : IsLinDerivation F p105 :=
  IsLinDerivation.ax d104 (inputMem 3 4 3 (by decide))

private def l106 : LC := {(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p106 : List LC := l106 :: p105
private theorem d106 : IsLinDerivation F p106 :=
  IsLinDerivation.weak (C := l105) d105
    (lineAt p105 0 (by decide +kernel)) (checkedWeak [(3,0),(3,1),(4,0),(4,1)] l105 l106
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l107 : LC := {(({(3,1)} : Finset V),true),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p107 : List LC := l107 :: p106
private theorem d107 : IsLinDerivation F p107 :=
  IsLinDerivation.res (C := l102) (D := l100) d106
    (lineAt p106 4 (by decide +kernel)) (lineAt p106 6 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l108 : LC := {(({(3,1)} : Finset V),false),(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p108 : List LC := l108 :: p107
private theorem d108 : IsLinDerivation F p108 :=
  IsLinDerivation.res (C := l106) (D := l104) d107
    (lineAt p107 1 (by decide +kernel)) (lineAt p107 3 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l109 : LC := {(({(3,0),(4,0)} : Finset V),true),(({(3,1),(4,1)} : Finset V),true)}
private def p109 : List LC := l109 :: p108
private theorem d109 : IsLinDerivation F p109 :=
  IsLinDerivation.res (C := l108) (D := l107) d108
    (lineAt p108 0 (by decide +kernel)) (lineAt p108 1 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l110 : LC := {(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),false),(({(1,0),(2,0)} : Finset V),true),(({(1,1),(2,1)} : Finset V),false)}
private def p110 : List LC := l110 :: p109
private theorem d110 : IsLinDerivation F p110 :=
  IsLinDerivation.weak (C := l21) d109
    (lineAt p109 88 (by decide +kernel)) (checkedWeak [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)] l21 l110
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def l111 : LC := {(({(0,0),(1,0)} : Finset V),true),(({(0,1),(1,1)} : Finset V),false),(({(1,0),(2,0)} : Finset V),true)}
private def p111 : List LC := l111 :: p110
private theorem d111 : IsLinDerivation F p111 :=
  IsLinDerivation.res (C := l110) (D := l54) d110
    (lineAt p110 0 (by decide +kernel)) (lineAt p110 56 (by decide +kernel))
    ⟨({(1,1),(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l112 : LC := {(({(0,0),(1,0)} : Finset V),true),(({(1,0),(2,0)} : Finset V),true)}
private def p112 : List LC := l112 :: p111
private theorem d112 : IsLinDerivation F p112 :=
  IsLinDerivation.res (C := l111) (D := l10) d111
    (lineAt p111 0 (by decide +kernel)) (lineAt p111 101 (by decide +kernel))
    ⟨({(0,1),(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem elevenPerPair : ∃ π : List (LinClause (Fin 5 × Fin 2)),
    IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) π ∧ π.length = 110 ∧
      (∀ i j : Fin 5, i < j →
        ({(({(i,0), (j,0)} : Finset V), true), (({(i,1), (j,1)} : Finset V), true)} : LC) ∈ π) :=
  ⟨p109, d109, by decide +kernel, by decide +kernel⟩

theorem threePigeons : ∃ π : List (LinClause (Fin 5 × Fin 2)),
    IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) π ∧ π.length = 113 ∧
      ({(({(0,0), (1,0)} : Finset V), true), (({(1,0), (2,0)} : Finset V), true)} : LC) ∈ π :=
  ⟨p112, d112, by decide +kernel, List.Mem.head _⟩

#print axioms elevenPerPair
#print axioms threePigeons

end Row133.Parity
