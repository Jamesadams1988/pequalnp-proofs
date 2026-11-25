import PEqualNP.Defs

namespace Row133.OnePair
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

theorem upper : ∃ π : List (LinClause (Fin 5 × Fin 2)),
    IsLinDerivation ((fun C => linOfClause C) '' BPHP 5 2) π ∧ π.length = 11 ∧
      ({(({(0,0), (1,0)} : Finset V), true), (({(0,1), (1,1)} : Finset V), true)} : LC) ∈ π :=
  ⟨p10, d10, by decide +kernel, List.Mem.head _⟩

#print axioms upper

end Row133.OnePair
