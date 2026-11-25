import PEqualNP.Defs

namespace Row133.Budget149
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


private def l0 : LC := linOfClause (inputClause 1 4 3)
private def p0 : List LC := l0 :: []
private theorem d0 : IsLinDerivation F p0 :=
  IsLinDerivation.ax IsLinDerivation.nil (inputMem 1 4 3 (by decide))

private def l1 : LC := linOfClause (inputClause 1 2 3)
private def p1 : List LC := l1 :: p0
private theorem d1 : IsLinDerivation F p1 :=
  IsLinDerivation.ax d0 (inputMem 1 2 3 (by decide))

private def l2 : LC := linOfClause (inputClause 2 4 2)
private def p2 : List LC := l2 :: p1
private theorem d2 : IsLinDerivation F p2 :=
  IsLinDerivation.ax d1 (inputMem 2 4 2 (by decide))

private def l3 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p3 : List LC := l3 :: p2
private theorem d3 : IsLinDerivation F p3 :=
  IsLinDerivation.res (C := l1) (D := l2) d2
    (lineAt p2 1 (by decide +kernel)) (lineAt p2 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l4 : LC := linOfClause (inputClause 1 3 3)
private def p4 : List LC := l4 :: p3
private theorem d4 : IsLinDerivation F p4 :=
  IsLinDerivation.ax d3 (inputMem 1 3 3 (by decide))

private def l5 : LC := linOfClause (inputClause 3 4 2)
private def p5 : List LC := l5 :: p4
private theorem d5 : IsLinDerivation F p5 :=
  IsLinDerivation.ax d4 (inputMem 3 4 2 (by decide))

private def l6 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p6 : List LC := l6 :: p5
private theorem d6 : IsLinDerivation F p6 :=
  IsLinDerivation.res (C := l4) (D := l5) d5
    (lineAt p5 1 (by decide +kernel)) (lineAt p5 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l7 : LC := linOfClause (inputClause 0 1 3)
private def p7 : List LC := l7 :: p6
private theorem d7 : IsLinDerivation F p7 :=
  IsLinDerivation.ax d6 (inputMem 0 1 3 (by decide))

private def l8 : LC := linOfClause (inputClause 0 4 2)
private def p8 : List LC := l8 :: p7
private theorem d8 : IsLinDerivation F p8 :=
  IsLinDerivation.ax d7 (inputMem 0 4 2 (by decide))

private def l9 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p9 : List LC := l9 :: p8
private theorem d9 : IsLinDerivation F p9 :=
  IsLinDerivation.res (C := l7) (D := l8) d8
    (lineAt p8 1 (by decide +kernel)) (lineAt p8 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l10 : LC := linOfClause (inputClause 2 3 1)
private def p10 : List LC := l10 :: p9
private theorem d10 : IsLinDerivation F p10 :=
  IsLinDerivation.ax d9 (inputMem 2 3 1 (by decide))

private def l11 : LC := linOfClause (inputClause 0 3 1)
private def p11 : List LC := l11 :: p10
private theorem d11 : IsLinDerivation F p11 :=
  IsLinDerivation.ax d10 (inputMem 0 3 1 (by decide))

private def l12 : LC := linOfClause (inputClause 0 2 0)
private def p12 : List LC := l12 :: p11
private theorem d12 : IsLinDerivation F p12 :=
  IsLinDerivation.ax d11 (inputMem 0 2 0 (by decide))

private def l13 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
private def p13 : List LC := l13 :: p12
private theorem d13 : IsLinDerivation F p13 :=
  IsLinDerivation.res (C := l11) (D := l12) d12
    (lineAt p12 1 (by decide +kernel)) (lineAt p12 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l14 : LC := {(({(0,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
private def p14 : List LC := l14 :: p13
private theorem d14 : IsLinDerivation F p14 :=
  IsLinDerivation.res (C := l10) (D := l13) d13
    (lineAt p13 3 (by decide +kernel)) (lineAt p13 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l15 : LC := linOfClause (inputClause 0 2 1)
private def p15 : List LC := l15 :: p14
private theorem d15 : IsLinDerivation F p15 :=
  IsLinDerivation.ax d14 (inputMem 0 2 1 (by decide))

private def l16 : LC := linOfClause (inputClause 0 3 0)
private def p16 : List LC := l16 :: p15
private theorem d16 : IsLinDerivation F p16 :=
  IsLinDerivation.ax d15 (inputMem 0 3 0 (by decide))

private def l17 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p17 : List LC := l17 :: p16
private theorem d17 : IsLinDerivation F p17 :=
  IsLinDerivation.res (C := l15) (D := l16) d16
    (lineAt p16 1 (by decide +kernel)) (lineAt p16 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l18 : LC := linOfClause (inputClause 2 3 0)
private def p18 : List LC := l18 :: p17
private theorem d18 : IsLinDerivation F p18 :=
  IsLinDerivation.ax d17 (inputMem 2 3 0 (by decide))

private def l19 : LC := {(({(0,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p19 : List LC := l19 :: p18
private theorem d19 : IsLinDerivation F p19 :=
  IsLinDerivation.res (C := l17) (D := l18) d18
    (lineAt p18 1 (by decide +kernel)) (lineAt p18 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l20 : LC := {(({(0,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p20 : List LC := l20 :: p19
private theorem d20 : IsLinDerivation F p20 :=
  IsLinDerivation.res (C := l14) (D := l19) d19
    (lineAt p19 5 (by decide +kernel)) (lineAt p19 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l21 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p21 : List LC := l21 :: p20
private theorem d21 : IsLinDerivation F p21 :=
  IsLinDerivation.res (C := l9) (D := l20) d20
    (lineAt p20 11 (by decide +kernel)) (lineAt p20 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l22 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p22 : List LC := l22 :: p21
private theorem d22 : IsLinDerivation F p22 :=
  IsLinDerivation.res (C := l6) (D := l21) d21
    (lineAt p21 15 (by decide +kernel)) (lineAt p21 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l23 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p23 : List LC := l23 :: p22
private theorem d23 : IsLinDerivation F p23 :=
  IsLinDerivation.res (C := l3) (D := l22) d22
    (lineAt p22 19 (by decide +kernel)) (lineAt p22 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l24 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p24 : List LC := l24 :: p23
private theorem d24 : IsLinDerivation F p24 :=
  IsLinDerivation.res (C := l0) (D := l23) d23
    (lineAt p23 23 (by decide +kernel)) (lineAt p23 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l25 : LC := linOfClause (inputClause 2 4 3)
private def p25 : List LC := l25 :: p24
private theorem d25 : IsLinDerivation F p25 :=
  IsLinDerivation.ax d24 (inputMem 2 4 3 (by decide))

private def l26 : LC := linOfClause (inputClause 1 2 2)
private def p26 : List LC := l26 :: p25
private theorem d26 : IsLinDerivation F p26 :=
  IsLinDerivation.ax d25 (inputMem 1 2 2 (by decide))

private def l27 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p27 : List LC := l27 :: p26
private theorem d27 : IsLinDerivation F p27 :=
  IsLinDerivation.res (C := l25) (D := l26) d26
    (lineAt p26 1 (by decide +kernel)) (lineAt p26 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l28 : LC := linOfClause (inputClause 3 4 3)
private def p28 : List LC := l28 :: p27
private theorem d28 : IsLinDerivation F p28 :=
  IsLinDerivation.ax d27 (inputMem 3 4 3 (by decide))

private def l29 : LC := linOfClause (inputClause 1 3 2)
private def p29 : List LC := l29 :: p28
private theorem d29 : IsLinDerivation F p29 :=
  IsLinDerivation.ax d28 (inputMem 1 3 2 (by decide))

private def l30 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p30 : List LC := l30 :: p29
private theorem d30 : IsLinDerivation F p30 :=
  IsLinDerivation.res (C := l28) (D := l29) d29
    (lineAt p29 1 (by decide +kernel)) (lineAt p29 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l31 : LC := linOfClause (inputClause 0 4 3)
private def p31 : List LC := l31 :: p30
private theorem d31 : IsLinDerivation F p31 :=
  IsLinDerivation.ax d30 (inputMem 0 4 3 (by decide))

private def l32 : LC := linOfClause (inputClause 0 1 2)
private def p32 : List LC := l32 :: p31
private theorem d32 : IsLinDerivation F p32 :=
  IsLinDerivation.ax d31 (inputMem 0 1 2 (by decide))

private def l33 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p33 : List LC := l33 :: p32
private theorem d33 : IsLinDerivation F p33 :=
  IsLinDerivation.res (C := l31) (D := l32) d32
    (lineAt p32 1 (by decide +kernel)) (lineAt p32 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l34 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p34 : List LC := l34 :: p33
private theorem d34 : IsLinDerivation F p34 :=
  IsLinDerivation.res (C := l33) (D := l20) d33
    (lineAt p33 0 (by decide +kernel)) (lineAt p33 13 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l35 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p35 : List LC := l35 :: p34
private theorem d35 : IsLinDerivation F p35 :=
  IsLinDerivation.res (C := l30) (D := l34) d34
    (lineAt p34 4 (by decide +kernel)) (lineAt p34 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l36 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p36 : List LC := l36 :: p35
private theorem d36 : IsLinDerivation F p36 :=
  IsLinDerivation.res (C := l27) (D := l35) d35
    (lineAt p35 8 (by decide +kernel)) (lineAt p35 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l37 : LC := linOfClause (inputClause 1 4 2)
private def p37 : List LC := l37 :: p36
private theorem d37 : IsLinDerivation F p37 :=
  IsLinDerivation.ax d36 (inputMem 1 4 2 (by decide))

private def l38 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p38 : List LC := l38 :: p37
private theorem d38 : IsLinDerivation F p38 :=
  IsLinDerivation.res (C := l36) (D := l37) d37
    (lineAt p37 1 (by decide +kernel)) (lineAt p37 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l39 : LC := {(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p39 : List LC := l39 :: p38
private theorem d39 : IsLinDerivation F p39 :=
  IsLinDerivation.res (C := l24) (D := l38) d38
    (lineAt p38 14 (by decide +kernel)) (lineAt p38 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l40 : LC := linOfClause (inputClause 2 3 2)
private def p40 : List LC := l40 :: p39
private theorem d40 : IsLinDerivation F p40 :=
  IsLinDerivation.ax d39 (inputMem 2 3 2 (by decide))

private def l41 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p41 : List LC := l41 :: p40
private theorem d41 : IsLinDerivation F p41 :=
  IsLinDerivation.res (C := l4) (D := l40) d40
    (lineAt p40 36 (by decide +kernel)) (lineAt p40 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l42 : LC := linOfClause (inputClause 0 2 2)
private def p42 : List LC := l42 :: p41
private theorem d42 : IsLinDerivation F p42 :=
  IsLinDerivation.ax d41 (inputMem 0 2 2 (by decide))

private def l43 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false)}
private def p43 : List LC := l43 :: p42
private theorem d43 : IsLinDerivation F p43 :=
  IsLinDerivation.res (C := l7) (D := l42) d42
    (lineAt p42 35 (by decide +kernel)) (lineAt p42 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l44 : LC := linOfClause (inputClause 3 4 1)
private def p44 : List LC := l44 :: p43
private theorem d44 : IsLinDerivation F p44 :=
  IsLinDerivation.ax d43 (inputMem 3 4 1 (by decide))

private def l45 : LC := linOfClause (inputClause 0 4 1)
private def p45 : List LC := l45 :: p44
private theorem d45 : IsLinDerivation F p45 :=
  IsLinDerivation.ax d44 (inputMem 0 4 1 (by decide))

private def l46 : LC := {(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p46 : List LC := l46 :: p45
private theorem d46 : IsLinDerivation F p46 :=
  IsLinDerivation.res (C := l45) (D := l16) d45
    (lineAt p45 0 (by decide +kernel)) (lineAt p45 29 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l47 : LC := {(({(0,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p47 : List LC := l47 :: p46
private theorem d47 : IsLinDerivation F p47 :=
  IsLinDerivation.res (C := l44) (D := l46) d46
    (lineAt p46 2 (by decide +kernel)) (lineAt p46 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l48 : LC := linOfClause (inputClause 0 4 0)
private def p48 : List LC := l48 :: p47
private theorem d48 : IsLinDerivation F p48 :=
  IsLinDerivation.ax d47 (inputMem 0 4 0 (by decide))

private def l49 : LC := {(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p49 : List LC := l49 :: p48
private theorem d49 : IsLinDerivation F p49 :=
  IsLinDerivation.res (C := l11) (D := l48) d48
    (lineAt p48 37 (by decide +kernel)) (lineAt p48 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l50 : LC := linOfClause (inputClause 3 4 0)
private def p50 : List LC := l50 :: p49
private theorem d50 : IsLinDerivation F p50 :=
  IsLinDerivation.ax d49 (inputMem 3 4 0 (by decide))

private def l51 : LC := {(({(0,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p51 : List LC := l51 :: p50
private theorem d51 : IsLinDerivation F p51 :=
  IsLinDerivation.res (C := l49) (D := l50) d50
    (lineAt p50 1 (by decide +kernel)) (lineAt p50 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l52 : LC := {(({(0,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p52 : List LC := l52 :: p51
private theorem d52 : IsLinDerivation F p52 :=
  IsLinDerivation.res (C := l47) (D := l51) d51
    (lineAt p51 4 (by decide +kernel)) (lineAt p51 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l53 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p53 : List LC := l53 :: p52
private theorem d53 : IsLinDerivation F p53 :=
  IsLinDerivation.res (C := l43) (D := l52) d52
    (lineAt p52 9 (by decide +kernel)) (lineAt p52 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l54 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p54 : List LC := l54 :: p53
private theorem d54 : IsLinDerivation F p54 :=
  IsLinDerivation.res (C := l41) (D := l53) d53
    (lineAt p53 12 (by decide +kernel)) (lineAt p53 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l55 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p55 : List LC := l55 :: p54
private theorem d55 : IsLinDerivation F p55 :=
  IsLinDerivation.res (C := l1) (D := l54) d54
    (lineAt p54 53 (by decide +kernel)) (lineAt p54 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l56 : LC := linOfClause (inputClause 2 3 3)
private def p56 : List LC := l56 :: p55
private theorem d56 : IsLinDerivation F p56 :=
  IsLinDerivation.ax d55 (inputMem 2 3 3 (by decide))

private def l57 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p57 : List LC := l57 :: p56
private theorem d57 : IsLinDerivation F p57 :=
  IsLinDerivation.res (C := l56) (D := l29) d56
    (lineAt p56 0 (by decide +kernel)) (lineAt p56 27 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l58 : LC := linOfClause (inputClause 0 2 3)
private def p58 : List LC := l58 :: p57
private theorem d58 : IsLinDerivation F p58 :=
  IsLinDerivation.ax d57 (inputMem 0 2 3 (by decide))

private def l59 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false)}
private def p59 : List LC := l59 :: p58
private theorem d59 : IsLinDerivation F p59 :=
  IsLinDerivation.res (C := l58) (D := l32) d58
    (lineAt p58 0 (by decide +kernel)) (lineAt p58 26 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l60 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p60 : List LC := l60 :: p59
private theorem d60 : IsLinDerivation F p60 :=
  IsLinDerivation.res (C := l59) (D := l52) d59
    (lineAt p59 0 (by decide +kernel)) (lineAt p59 7 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l61 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p61 : List LC := l61 :: p60
private theorem d61 : IsLinDerivation F p61 :=
  IsLinDerivation.res (C := l57) (D := l60) d60
    (lineAt p60 3 (by decide +kernel)) (lineAt p60 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l62 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p62 : List LC := l62 :: p61
private theorem d62 : IsLinDerivation F p62 :=
  IsLinDerivation.res (C := l61) (D := l26) d61
    (lineAt p61 0 (by decide +kernel)) (lineAt p61 35 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l63 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p63 : List LC := l63 :: p62
private theorem d63 : IsLinDerivation F p63 :=
  IsLinDerivation.res (C := l55) (D := l62) d62
    (lineAt p62 7 (by decide +kernel)) (lineAt p62 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l64 : LC := linOfClause (inputClause 2 4 1)
private def p64 : List LC := l64 :: p63
private theorem d64 : IsLinDerivation F p64 :=
  IsLinDerivation.ax d63 (inputMem 2 4 1 (by decide))

private def l65 : LC := linOfClause (inputClause 0 3 2)
private def p65 : List LC := l65 :: p64
private theorem d65 : IsLinDerivation F p65 :=
  IsLinDerivation.ax d64 (inputMem 0 3 2 (by decide))

private def l66 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
private def p66 : List LC := l66 :: p65
private theorem d66 : IsLinDerivation F p66 :=
  IsLinDerivation.res (C := l7) (D := l65) d65
    (lineAt p65 58 (by decide +kernel)) (lineAt p65 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l67 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p67 : List LC := l67 :: p66
private theorem d67 : IsLinDerivation F p67 :=
  IsLinDerivation.res (C := l4) (D := l66) d66
    (lineAt p66 62 (by decide +kernel)) (lineAt p66 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l68 : LC := linOfClause (inputClause 0 3 3)
private def p68 : List LC := l68 :: p67
private theorem d68 : IsLinDerivation F p68 :=
  IsLinDerivation.ax d67 (inputMem 0 3 3 (by decide))

private def l69 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p69 : List LC := l69 :: p68
private theorem d69 : IsLinDerivation F p69 :=
  IsLinDerivation.res (C := l68) (D := l32) d68
    (lineAt p68 0 (by decide +kernel)) (lineAt p68 36 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l70 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p70 : List LC := l70 :: p69
private theorem d70 : IsLinDerivation F p70 :=
  IsLinDerivation.res (C := l69) (D := l29) d69
    (lineAt p69 0 (by decide +kernel)) (lineAt p69 40 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l71 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p71 : List LC := l71 :: p70
private theorem d71 : IsLinDerivation F p71 :=
  IsLinDerivation.res (C := l67) (D := l70) d70
    (lineAt p70 3 (by decide +kernel)) (lineAt p70 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l72 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p72 : List LC := l72 :: p71
private theorem d72 : IsLinDerivation F p72 :=
  IsLinDerivation.res (C := l10) (D := l50) d71
    (lineAt p71 61 (by decide +kernel)) (lineAt p71 21 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l73 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p73 : List LC := l73 :: p72
private theorem d73 : IsLinDerivation F p73 :=
  IsLinDerivation.res (C := l71) (D := l72) d72
    (lineAt p72 1 (by decide +kernel)) (lineAt p72 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l74 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p74 : List LC := l74 :: p73
private theorem d74 : IsLinDerivation F p74 :=
  IsLinDerivation.res (C := l15) (D := l48) d73
    (lineAt p73 58 (by decide +kernel)) (lineAt p73 25 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l75 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p75 : List LC := l75 :: p74
private theorem d75 : IsLinDerivation F p75 :=
  IsLinDerivation.res (C := l73) (D := l74) d74
    (lineAt p74 1 (by decide +kernel)) (lineAt p74 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l76 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p76 : List LC := l76 :: p75
private theorem d76 : IsLinDerivation F p76 :=
  IsLinDerivation.res (C := l64) (D := l75) d75
    (lineAt p75 11 (by decide +kernel)) (lineAt p75 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l77 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p77 : List LC := l77 :: p76
private theorem d77 : IsLinDerivation F p77 :=
  IsLinDerivation.res (C := l45) (D := l12) d76
    (lineAt p76 31 (by decide +kernel)) (lineAt p76 64 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l78 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p78 : List LC := l78 :: p77
private theorem d78 : IsLinDerivation F p78 :=
  IsLinDerivation.res (C := l71) (D := l77) d77
    (lineAt p77 6 (by decide +kernel)) (lineAt p77 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l79 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p79 : List LC := l79 :: p78
private theorem d79 : IsLinDerivation F p79 :=
  IsLinDerivation.res (C := l44) (D := l18) d78
    (lineAt p78 34 (by decide +kernel)) (lineAt p78 60 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l80 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p80 : List LC := l80 :: p79
private theorem d80 : IsLinDerivation F p80 :=
  IsLinDerivation.res (C := l78) (D := l79) d79
    (lineAt p79 1 (by decide +kernel)) (lineAt p79 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l81 : LC := linOfClause (inputClause 2 4 0)
private def p81 : List LC := l81 :: p80
private theorem d81 : IsLinDerivation F p81 :=
  IsLinDerivation.ax d80 (inputMem 2 4 0 (by decide))

private def l82 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p82 : List LC := l82 :: p81
private theorem d82 : IsLinDerivation F p82 :=
  IsLinDerivation.res (C := l80) (D := l81) d81
    (lineAt p81 1 (by decide +kernel)) (lineAt p81 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l83 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p83 : List LC := l83 :: p82
private theorem d83 : IsLinDerivation F p83 :=
  IsLinDerivation.res (C := l76) (D := l82) d82
    (lineAt p82 6 (by decide +kernel)) (lineAt p82 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l84 : LC := {(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p84 : List LC := l84 :: p83
private theorem d84 : IsLinDerivation F p84 :=
  IsLinDerivation.res (C := l63) (D := l83) d83
    (lineAt p83 20 (by decide +kernel)) (lineAt p83 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l85 : LC := {(({(1,1)} : Finset V),false)}
private def p85 : List LC := l85 :: p84
private theorem d85 : IsLinDerivation F p85 :=
  IsLinDerivation.res (C := l39) (D := l84) d84
    (lineAt p84 45 (by decide +kernel)) (lineAt p84 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l86 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p86 : List LC := l86 :: p85
private theorem d86 : IsLinDerivation F p86 :=
  IsLinDerivation.res (C := l31) (D := l42) d85
    (lineAt p85 54 (by decide +kernel)) (lineAt p85 43 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l87 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p87 : List LC := l87 :: p86
private theorem d87 : IsLinDerivation F p87 :=
  IsLinDerivation.res (C := l28) (D := l40) d86
    (lineAt p86 58 (by decide +kernel)) (lineAt p86 46 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l88 : LC := linOfClause (inputClause 1 3 1)
private def p88 : List LC := l88 :: p87
private theorem d88 : IsLinDerivation F p88 :=
  IsLinDerivation.ax d87 (inputMem 1 3 1 (by decide))

private def l89 : LC := linOfClause (inputClause 0 1 1)
private def p89 : List LC := l89 :: p88
private theorem d89 : IsLinDerivation F p89 :=
  IsLinDerivation.ax d88 (inputMem 0 1 1 (by decide))

private def l90 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p90 : List LC := l90 :: p89
private theorem d90 : IsLinDerivation F p90 :=
  IsLinDerivation.res (C := l89) (D := l16) d89
    (lineAt p89 0 (by decide +kernel)) (lineAt p89 73 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l91 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p91 : List LC := l91 :: p90
private theorem d91 : IsLinDerivation F p91 :=
  IsLinDerivation.res (C := l88) (D := l90) d90
    (lineAt p90 2 (by decide +kernel)) (lineAt p90 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l92 : LC := linOfClause (inputClause 0 1 0)
private def p92 : List LC := l92 :: p91
private theorem d92 : IsLinDerivation F p92 :=
  IsLinDerivation.ax d91 (inputMem 0 1 0 (by decide))

private def l93 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
private def p93 : List LC := l93 :: p92
private theorem d93 : IsLinDerivation F p93 :=
  IsLinDerivation.res (C := l11) (D := l92) d92
    (lineAt p92 81 (by decide +kernel)) (lineAt p92 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l94 : LC := linOfClause (inputClause 1 3 0)
private def p94 : List LC := l94 :: p93
private theorem d94 : IsLinDerivation F p94 :=
  IsLinDerivation.ax d93 (inputMem 1 3 0 (by decide))

private def l95 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p95 : List LC := l95 :: p94
private theorem d95 : IsLinDerivation F p95 :=
  IsLinDerivation.res (C := l93) (D := l94) d94
    (lineAt p94 1 (by decide +kernel)) (lineAt p94 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l96 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p96 : List LC := l96 :: p95
private theorem d96 : IsLinDerivation F p96 :=
  IsLinDerivation.res (C := l91) (D := l95) d95
    (lineAt p95 4 (by decide +kernel)) (lineAt p95 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l97 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p97 : List LC := l97 :: p96
private theorem d97 : IsLinDerivation F p97 :=
  IsLinDerivation.res (C := l87) (D := l96) d96
    (lineAt p96 9 (by decide +kernel)) (lineAt p96 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l98 : LC := {(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p98 : List LC := l98 :: p97
private theorem d98 : IsLinDerivation F p98 :=
  IsLinDerivation.res (C := l86) (D := l97) d97
    (lineAt p97 11 (by decide +kernel)) (lineAt p97 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l99 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p99 : List LC := l99 :: p98
private theorem d99 : IsLinDerivation F p99 :=
  IsLinDerivation.res (C := l25) (D := l98) d98
    (lineAt p98 73 (by decide +kernel)) (lineAt p98 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l100 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p100 : List LC := l100 :: p99
private theorem d100 : IsLinDerivation F p100 :=
  IsLinDerivation.res (C := l58) (D := l8) d99
    (lineAt p99 41 (by decide +kernel)) (lineAt p99 91 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l101 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p101 : List LC := l101 :: p100
private theorem d101 : IsLinDerivation F p101 :=
  IsLinDerivation.res (C := l56) (D := l5) d100
    (lineAt p100 44 (by decide +kernel)) (lineAt p100 95 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l102 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p102 : List LC := l102 :: p101
private theorem d102 : IsLinDerivation F p102 :=
  IsLinDerivation.res (C := l101) (D := l96) d101
    (lineAt p101 0 (by decide +kernel)) (lineAt p101 5 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l103 : LC := {(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p103 : List LC := l103 :: p102
private theorem d103 : IsLinDerivation F p103 :=
  IsLinDerivation.res (C := l100) (D := l102) d102
    (lineAt p102 2 (by decide +kernel)) (lineAt p102 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l104 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p104 : List LC := l104 :: p103
private theorem d104 : IsLinDerivation F p104 :=
  IsLinDerivation.res (C := l103) (D := l2) d103
    (lineAt p103 0 (by decide +kernel)) (lineAt p103 101 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l105 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p105 : List LC := l105 :: p104
private theorem d105 : IsLinDerivation F p105 :=
  IsLinDerivation.res (C := l99) (D := l104) d104
    (lineAt p104 5 (by decide +kernel)) (lineAt p104 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l106 : LC := linOfClause (inputClause 1 2 1)
private def p106 : List LC := l106 :: p105
private theorem d106 : IsLinDerivation F p106 :=
  IsLinDerivation.ax d105 (inputMem 1 2 1 (by decide))

private def l107 : LC := {(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p107 : List LC := l107 :: p106
private theorem d107 : IsLinDerivation F p107 :=
  IsLinDerivation.res (C := l31) (D := l65) d106
    (lineAt p106 75 (by decide +kernel)) (lineAt p106 41 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l108 : LC := {(({(0,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p108 : List LC := l108 :: p107
private theorem d108 : IsLinDerivation F p108 :=
  IsLinDerivation.res (C := l28) (D := l107) d107
    (lineAt p107 79 (by decide +kernel)) (lineAt p107 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l109 : LC := {(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p109 : List LC := l109 :: p108
private theorem d109 : IsLinDerivation F p109 :=
  IsLinDerivation.res (C := l68) (D := l8) d108
    (lineAt p108 40 (by decide +kernel)) (lineAt p108 100 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l110 : LC := {(({(0,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p110 : List LC := l110 :: p109
private theorem d110 : IsLinDerivation F p110 :=
  IsLinDerivation.res (C := l109) (D := l5) d109
    (lineAt p109 0 (by decide +kernel)) (lineAt p109 104 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l111 : LC := {(({(0,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p111 : List LC := l111 :: p110
private theorem d111 : IsLinDerivation F p111 :=
  IsLinDerivation.res (C := l108) (D := l110) d110
    (lineAt p110 2 (by decide +kernel)) (lineAt p110 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l112 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p112 : List LC := l112 :: p111
private theorem d112 : IsLinDerivation F p112 :=
  IsLinDerivation.res (C := l10) (D := l94) d111
    (lineAt p111 101 (by decide +kernel)) (lineAt p111 17 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l113 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p113 : List LC := l113 :: p112
private theorem d113 : IsLinDerivation F p113 :=
  IsLinDerivation.res (C := l111) (D := l112) d112
    (lineAt p112 1 (by decide +kernel)) (lineAt p112 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l114 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
private def p114 : List LC := l114 :: p113
private theorem d114 : IsLinDerivation F p114 :=
  IsLinDerivation.res (C := l15) (D := l92) d113
    (lineAt p113 98 (by decide +kernel)) (lineAt p113 21 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l115 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p115 : List LC := l115 :: p114
private theorem d115 : IsLinDerivation F p115 :=
  IsLinDerivation.res (C := l113) (D := l114) d114
    (lineAt p114 1 (by decide +kernel)) (lineAt p114 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l116 : LC := {(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p116 : List LC := l116 :: p115
private theorem d116 : IsLinDerivation F p116 :=
  IsLinDerivation.res (C := l106) (D := l115) d115
    (lineAt p115 9 (by decide +kernel)) (lineAt p115 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l117 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true)}
private def p117 : List LC := l117 :: p116
private theorem d117 : IsLinDerivation F p117 :=
  IsLinDerivation.res (C := l89) (D := l12) d116
    (lineAt p116 27 (by decide +kernel)) (lineAt p116 104 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l118 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
private def p118 : List LC := l118 :: p117
private theorem d118 : IsLinDerivation F p118 :=
  IsLinDerivation.res (C := l111) (D := l117) d117
    (lineAt p117 6 (by decide +kernel)) (lineAt p117 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l119 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
private def p119 : List LC := l119 :: p118
private theorem d119 : IsLinDerivation F p119 :=
  IsLinDerivation.res (C := l88) (D := l18) d118
    (lineAt p118 30 (by decide +kernel)) (lineAt p118 100 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l120 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p120 : List LC := l120 :: p119
private theorem d120 : IsLinDerivation F p120 :=
  IsLinDerivation.res (C := l118) (D := l119) d119
    (lineAt p119 1 (by decide +kernel)) (lineAt p119 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l121 : LC := linOfClause (inputClause 1 2 0)
private def p121 : List LC := l121 :: p120
private theorem d121 : IsLinDerivation F p121 :=
  IsLinDerivation.ax d120 (inputMem 1 2 0 (by decide))

private def l122 : LC := {(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p122 : List LC := l122 :: p121
private theorem d122 : IsLinDerivation F p122 :=
  IsLinDerivation.res (C := l120) (D := l121) d121
    (lineAt p121 1 (by decide +kernel)) (lineAt p121 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l123 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p123 : List LC := l123 :: p122
private theorem d123 : IsLinDerivation F p123 :=
  IsLinDerivation.res (C := l116) (D := l122) d122
    (lineAt p122 6 (by decide +kernel)) (lineAt p122 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l124 : LC := {(({(1,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
private def p124 : List LC := l124 :: p123
private theorem d124 : IsLinDerivation F p124 :=
  IsLinDerivation.res (C := l105) (D := l123) d123
    (lineAt p123 18 (by decide +kernel)) (lineAt p123 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l125 : LC := linOfClause (inputClause 1 4 1)
private def p125 : List LC := l125 :: p124
private theorem d125 : IsLinDerivation F p125 :=
  IsLinDerivation.ax d124 (inputMem 1 4 1 (by decide))

private def l126 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p126 : List LC := l126 :: p125
private theorem d126 : IsLinDerivation F p126 :=
  IsLinDerivation.res (C := l68) (D := l42) d125
    (lineAt p125 57 (by decide +kernel)) (lineAt p125 83 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l127 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p127 : List LC := l127 :: p126
private theorem d127 : IsLinDerivation F p127 :=
  IsLinDerivation.res (C := l56) (D := l126) d126
    (lineAt p126 70 (by decide +kernel)) (lineAt p126 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l128 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
private def p128 : List LC := l128 :: p127
private theorem d128 : IsLinDerivation F p128 :=
  IsLinDerivation.res (C := l58) (D := l65) d127
    (lineAt p127 69 (by decide +kernel)) (lineAt p127 62 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l129 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
private def p129 : List LC := l129 :: p128
private theorem d129 : IsLinDerivation F p129 :=
  IsLinDerivation.res (C := l128) (D := l40) d128
    (lineAt p128 0 (by decide +kernel)) (lineAt p128 88 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l130 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
private def p130 : List LC := l130 :: p129
private theorem d130 : IsLinDerivation F p130 :=
  IsLinDerivation.res (C := l127) (D := l129) d129
    (lineAt p129 2 (by decide +kernel)) (lineAt p129 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l131 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p131 : List LC := l131 :: p130
private theorem d131 : IsLinDerivation F p131 :=
  IsLinDerivation.res (C := l89) (D := l48) d130
    (lineAt p130 41 (by decide +kernel)) (lineAt p130 82 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l132 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p132 : List LC := l132 :: p131
private theorem d132 : IsLinDerivation F p132 :=
  IsLinDerivation.res (C := l130) (D := l131) d131
    (lineAt p131 1 (by decide +kernel)) (lineAt p131 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l133 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p133 : List LC := l133 :: p132
private theorem d133 : IsLinDerivation F p133 :=
  IsLinDerivation.res (C := l88) (D := l50) d132
    (lineAt p132 44 (by decide +kernel)) (lineAt p132 82 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l134 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p134 : List LC := l134 :: p133
private theorem d134 : IsLinDerivation F p134 :=
  IsLinDerivation.res (C := l132) (D := l133) d133
    (lineAt p133 1 (by decide +kernel)) (lineAt p133 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l135 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p135 : List LC := l135 :: p134
private theorem d135 : IsLinDerivation F p135 :=
  IsLinDerivation.res (C := l106) (D := l81) d134
    (lineAt p134 28 (by decide +kernel)) (lineAt p134 53 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l136 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p136 : List LC := l136 :: p135
private theorem d136 : IsLinDerivation F p136 :=
  IsLinDerivation.res (C := l134) (D := l135) d135
    (lineAt p135 1 (by decide +kernel)) (lineAt p135 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l137 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p137 : List LC := l137 :: p136
private theorem d137 : IsLinDerivation F p137 :=
  IsLinDerivation.res (C := l125) (D := l136) d136
    (lineAt p136 11 (by decide +kernel)) (lineAt p136 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l138 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p138 : List LC := l138 :: p137
private theorem d138 : IsLinDerivation F p138 :=
  IsLinDerivation.res (C := l45) (D := l92) d137
    (lineAt p137 92 (by decide +kernel)) (lineAt p137 45 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l139 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p139 : List LC := l139 :: p138
private theorem d139 : IsLinDerivation F p139 :=
  IsLinDerivation.res (C := l130) (D := l138) d138
    (lineAt p138 8 (by decide +kernel)) (lineAt p138 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l140 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p140 : List LC := l140 :: p139
private theorem d140 : IsLinDerivation F p140 :=
  IsLinDerivation.res (C := l44) (D := l94) d139
    (lineAt p139 95 (by decide +kernel)) (lineAt p139 45 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l141 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p141 : List LC := l141 :: p140
private theorem d141 : IsLinDerivation F p141 :=
  IsLinDerivation.res (C := l139) (D := l140) d140
    (lineAt p140 1 (by decide +kernel)) (lineAt p140 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l142 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p142 : List LC := l142 :: p141
private theorem d142 : IsLinDerivation F p142 :=
  IsLinDerivation.res (C := l64) (D := l121) d141
    (lineAt p141 77 (by decide +kernel)) (lineAt p141 20 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l143 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
private def p143 : List LC := l143 :: p142
private theorem d143 : IsLinDerivation F p143 :=
  IsLinDerivation.res (C := l141) (D := l142) d142
    (lineAt p142 1 (by decide +kernel)) (lineAt p142 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l144 : LC := linOfClause (inputClause 1 4 0)
private def p144 : List LC := l144 :: p143
private theorem d144 : IsLinDerivation F p144 :=
  IsLinDerivation.ax d143 (inputMem 1 4 0 (by decide))

private def l145 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p145 : List LC := l145 :: p144
private theorem d145 : IsLinDerivation F p145 :=
  IsLinDerivation.res (C := l143) (D := l144) d144
    (lineAt p144 1 (by decide +kernel)) (lineAt p144 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l146 : LC := {(({(1,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
private def p146 : List LC := l146 :: p145
private theorem d146 : IsLinDerivation F p146 :=
  IsLinDerivation.res (C := l137) (D := l145) d145
    (lineAt p145 8 (by decide +kernel)) (lineAt p145 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l147 : LC := {(({(1,1)} : Finset V),true)}
private def p147 : List LC := l147 :: p146
private theorem d147 : IsLinDerivation F p147 :=
  IsLinDerivation.res (C := l124) (D := l146) d146
    (lineAt p146 22 (by decide +kernel)) (lineAt p146 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

private def l148 : LC := ∅
private def p148 : List LC := l148 :: p147
private theorem d148 : IsLinDerivation F p148 :=
  IsLinDerivation.res (C := l85) (D := l147) d147
    (lineAt p147 62 (by decide +kernel)) (lineAt p147 0 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem _root_.Row133.refutation149 :
    ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)),
      PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧
      π.length ≤ 149 :=
  ⟨p148,⟨d148,List.Mem.head _⟩,by decide +kernel⟩

end Row133.Budget149
