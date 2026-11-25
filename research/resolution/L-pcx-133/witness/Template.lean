import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_133
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

-- SEMANTIC WEAKENING
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
-- END SEMANTIC WEAKENING

end PEqualNP.Outside.L_pcx_133
