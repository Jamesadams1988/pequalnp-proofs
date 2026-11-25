import PEqualNP.Defs

namespace Row169.Certificate
open PEqualNP.ProofComplexity
private abbrev V := Fin 5 × Fin 4
private abbrev Cl := Clause V

/-- Parent positions are relative to the newest already available clause. -/
private inductive Step where
  | pigeon (p : Fin 5)
  | hole (p q : Fin 5) (h : Fin 4)
  | resolve (pos neg : ℕ) (v : V) (out : Cl)

private def Step.line : Step → Cl
  | .pigeon p => Finset.univ.image (fun h : Fin 4 => ((p,h),true))
  | .hole p q h => {((p,h),false),((q,h),false)}
  | .resolve _ _ _ out => out

private def valid (s : Step) (bank : List Cl) : Bool :=
  match s with
  | .pigeon _ => true
  | .hole p q _ => decide (p ≠ q)
  | .resolve i j v out =>
    match bank[i]?, bank[j]? with
    | some a, some b => decide ((v,true) ∈ a ∧ (v,false) ∈ b ∧ out = a.erase (v,true) ∪ b.erase (v,false))
    | _, _ => false

private theorem validStep (s : Step) (bank : List Cl) (prior : IsDerivation (PHP 5 4) bank)
    (ok : valid s bank = true) : IsDerivation (PHP 5 4) (s.line :: bank) := by
  cases s with
  | pigeon p => exact .ax prior (.inl ⟨p,rfl⟩)
  | hole p q h => exact .ax prior (.inr ⟨p,q,h,of_decide_eq_true ok,rfl⟩)
  | resolve i j v out =>
    cases ha : bank[i]? with
    | none => simp [valid,ha] at ok
    | some a =>
      cases hb : bank[j]? with
      | none => simp [valid,ha,hb] at ok
      | some b =>
        have rule : (v,true) ∈ a ∧ (v,false) ∈ b ∧ out = a.erase (v,true) ∪ b.erase (v,false) := by
          simpa [valid,ha,hb] using ok
        exact .res prior (List.mem_of_getElem? ha) (List.mem_of_getElem? hb) ⟨v,rule⟩

private def verify : List Step → List Cl → Bool
  | [], _ => true
  | s :: ss, bank => valid s bank && verify ss (s.line :: bank)

private theorem verifySound (ss : List Step) (bank : List Cl) (prior : IsDerivation (PHP 5 4) bank)
    (ok : verify ss bank = true) : IsDerivation (PHP 5 4) ((ss.map Step.line).reverse ++ bank) := by
  induction ss generalizing bank with
  | nil => simpa using prior
  | cons s ss ih =>
    have h : valid s bank = true ∧ verify ss (s.line :: bank) = true := by
      simpa only [verify,Bool.and_eq_true] using ok
    simpa using ih (s.line :: bank) (validStep s bank prior h.1) h.2

end Row169.Certificate
