import PEqualNP.Defs

namespace Row169.Budget377
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

private def steps : List Step := [
  .pigeon 0,
  .pigeon 4,
  .hole 0 4 3,
  .resolve 1 0 (4,3) {((0,3),false),((4,0),true),((4,1),true),((4,2),true)},
  .pigeon 3,
  .hole 3 4 2,
  .resolve 1 0 (3,2) {((3,0),true),((3,1),true),((3,3),true),((4,2),false)},
  .pigeon 1,
  .hole 1 3 1,
  .resolve 1 0 (1,1) {((1,0),true),((1,2),true),((1,3),true),((3,1),false)},
  .pigeon 2,
  .hole 2 3 1,
  .resolve 1 0 (2,1) {((2,0),true),((2,2),true),((2,3),true),((3,1),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,2),true),((2,3),true),((3,1),false)},
  .resolve 5 0 (1,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,1),false)},
  .resolve 9 0 (3,1) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),true),((3,3),true),((4,2),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 1,
  .resolve 1 0 (2,1) {((1,1),false),((2,0),true),((2,2),true),((2,3),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,1),false),((2,2),true),((2,3),true),((3,0),false)},
  .resolve 5 0 (1,1) {((1,0),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,3),true),((4,2),false)},
  .hole 2 4 2,
  .resolve 1 0 (2,2) {((1,2),true),((1,3),true),((2,3),true),((3,3),true),((4,2),false)},
  .hole 1 4 2,
  .resolve 1 0 (1,2) {((1,3),true),((2,3),true),((3,3),true),((4,2),false)},
  .resolve 27 0 (4,2) {((0,3),false),((1,3),true),((2,3),true),((3,3),true),((4,0),true),((4,1),true)},
  .pigeon 3,
  .pigeon 1,
  .hole 1 3 2,
  .resolve 1 0 (1,2) {((1,0),true),((1,1),true),((1,3),true),((3,2),false)},
  .pigeon 2,
  .hole 2 3 2,
  .resolve 1 0 (2,2) {((2,0),true),((2,1),true),((2,3),true),((3,2),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,1),true),((2,3),true),((3,2),false)},
  .resolve 5 0 (1,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,2),false)},
  .resolve 9 0 (3,2) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,1),true),((3,3),true)},
  .hole 3 4 1,
  .resolve 1 0 (3,1) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 2,
  .resolve 1 0 (2,2) {((1,2),false),((2,0),true),((2,1),true),((2,3),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,2),false),((2,1),true),((2,3),true),((3,0),false)},
  .resolve 5 0 (1,2) {((1,0),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,3),true),((4,1),false)},
  .hole 2 4 1,
  .resolve 1 0 (2,1) {((1,1),true),((1,3),true),((2,3),true),((3,3),true),((4,1),false)},
  .hole 1 4 1,
  .resolve 1 0 (1,1) {((1,3),true),((2,3),true),((3,3),true),((4,1),false)},
  .resolve 27 0 (4,1) {((0,3),false),((1,3),true),((2,3),true),((3,3),true),((4,0),true)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 2,
  .resolve 1 0 (2,2) {((1,2),false),((2,0),true),((2,1),true),((2,3),true)},
  .pigeon 3,
  .hole 1 3 2,
  .resolve 1 0 (3,2) {((1,2),false),((3,0),true),((3,1),true),((3,3),true)},
  .hole 2 3 1,
  .resolve 1 0 (3,1) {((1,2),false),((2,1),false),((3,0),true),((3,3),true)},
  .resolve 5 0 (2,1) {((1,2),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true)},
  .resolve 9 0 (1,2) {((1,0),true),((1,1),true),((1,3),true),((2,0),true),((2,3),true),((3,0),true),((3,3),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 2,
  .resolve 1 0 (3,2) {((2,2),false),((3,0),true),((3,1),true),((3,3),true)},
  .hole 1 3 1,
  .resolve 1 0 (3,1) {((1,1),false),((2,2),false),((3,0),true),((3,3),true)},
  .resolve 5 0 (2,2) {((1,1),false),((2,0),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true)},
  .hole 1 2 1,
  .resolve 1 0 (2,1) {((1,1),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true)},
  .resolve 9 0 (1,1) {((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,0),true),((3,3),true)},
  .hole 3 4 0,
  .resolve 1 0 (3,0) {((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,3),true),((4,0),false)},
  .hole 2 4 0,
  .resolve 1 0 (2,0) {((1,0),true),((1,3),true),((2,3),true),((3,3),true),((4,0),false)},
  .hole 1 4 0,
  .resolve 1 0 (1,0) {((1,3),true),((2,3),true),((3,3),true),((4,0),false)},
  .resolve 27 0 (4,0) {((0,3),false),((1,3),true),((2,3),true),((3,3),true)},
  .hole 0 3 3,
  .resolve 1 0 (3,3) {((0,3),false),((1,3),true),((2,3),true)},
  .hole 0 2 3,
  .resolve 1 0 (2,3) {((0,3),false),((1,3),true)},
  .hole 0 1 3,
  .resolve 1 0 (1,3) {((0,3),false)},
  .resolve 93 0 (0,3) {((0,0),true),((0,1),true),((0,2),true)},
  .pigeon 4,
  .pigeon 3,
  .hole 3 4 3,
  .resolve 1 0 (3,3) {((3,0),true),((3,1),true),((3,2),true),((4,3),false)},
  .pigeon 1,
  .hole 1 3 1,
  .resolve 1 0 (1,1) {((1,0),true),((1,2),true),((1,3),true),((3,1),false)},
  .pigeon 2,
  .hole 2 3 1,
  .resolve 1 0 (2,1) {((2,0),true),((2,2),true),((2,3),true),((3,1),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,2),true),((2,3),true),((3,1),false)},
  .resolve 5 0 (1,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,1),false)},
  .resolve 9 0 (3,1) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),true),((3,2),true),((4,3),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 1,
  .resolve 1 0 (2,1) {((1,1),false),((2,0),true),((2,2),true),((2,3),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,1),false),((2,2),true),((2,3),true),((3,0),false)},
  .resolve 5 0 (1,1) {((1,0),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,2),true),((4,3),false)},
  .hole 2 4 3,
  .resolve 1 0 (2,3) {((1,2),true),((1,3),true),((2,2),true),((3,2),true),((4,3),false)},
  .hole 1 4 3,
  .resolve 1 0 (1,3) {((1,2),true),((2,2),true),((3,2),true),((4,3),false)},
  .resolve 27 0 (4,3) {((1,2),true),((2,2),true),((3,2),true),((4,0),true),((4,1),true),((4,2),true)},
  .hole 0 4 2,
  .resolve 1 0 (4,2) {((0,2),false),((1,2),true),((2,2),true),((3,2),true),((4,0),true),((4,1),true)},
  .pigeon 3,
  .pigeon 1,
  .hole 1 3 3,
  .resolve 1 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((3,3),false)},
  .pigeon 2,
  .hole 2 3 3,
  .resolve 1 0 (2,3) {((2,0),true),((2,1),true),((2,2),true),((3,3),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,1),true),((2,2),true),((3,3),false)},
  .resolve 5 0 (1,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,3),false)},
  .resolve 9 0 (3,3) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((3,2),true)},
  .hole 3 4 1,
  .resolve 1 0 (3,1) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 3,
  .resolve 1 0 (2,3) {((1,3),false),((2,0),true),((2,1),true),((2,2),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,3),false),((2,1),true),((2,2),true),((3,0),false)},
  .resolve 5 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,2),true),((4,1),false)},
  .hole 2 4 1,
  .resolve 1 0 (2,1) {((1,1),true),((1,2),true),((2,2),true),((3,2),true),((4,1),false)},
  .hole 1 4 1,
  .resolve 1 0 (1,1) {((1,2),true),((2,2),true),((3,2),true),((4,1),false)},
  .resolve 27 0 (4,1) {((0,2),false),((1,2),true),((2,2),true),((3,2),true),((4,0),true)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 3,
  .resolve 1 0 (2,3) {((1,3),false),((2,0),true),((2,1),true),((2,2),true)},
  .pigeon 3,
  .hole 1 3 3,
  .resolve 1 0 (3,3) {((1,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .hole 2 3 1,
  .resolve 1 0 (3,1) {((1,3),false),((2,1),false),((3,0),true),((3,2),true)},
  .resolve 5 0 (2,1) {((1,3),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true)},
  .resolve 9 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((2,2),true),((3,0),true),((3,2),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 3,
  .resolve 1 0 (3,3) {((2,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .hole 1 3 1,
  .resolve 1 0 (3,1) {((1,1),false),((2,3),false),((3,0),true),((3,2),true)},
  .resolve 5 0 (2,3) {((1,1),false),((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true)},
  .hole 1 2 1,
  .resolve 1 0 (2,1) {((1,1),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true)},
  .resolve 9 0 (1,1) {((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,0),true),((3,2),true)},
  .hole 3 4 0,
  .resolve 1 0 (3,0) {((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,2),true),((4,0),false)},
  .hole 2 4 0,
  .resolve 1 0 (2,0) {((1,0),true),((1,2),true),((2,2),true),((3,2),true),((4,0),false)},
  .hole 1 4 0,
  .resolve 1 0 (1,0) {((1,2),true),((2,2),true),((3,2),true),((4,0),false)},
  .resolve 27 0 (4,0) {((0,2),false),((1,2),true),((2,2),true),((3,2),true)},
  .hole 0 3 2,
  .resolve 1 0 (3,2) {((0,2),false),((1,2),true),((2,2),true)},
  .hole 0 2 2,
  .resolve 1 0 (2,2) {((0,2),false),((1,2),true)},
  .hole 0 1 2,
  .resolve 1 0 (1,2) {((0,2),false)},
  .resolve 93 0 (0,2) {((0,0),true),((0,1),true)},
  .pigeon 4,
  .pigeon 3,
  .hole 3 4 3,
  .resolve 1 0 (3,3) {((3,0),true),((3,1),true),((3,2),true),((4,3),false)},
  .pigeon 1,
  .hole 1 3 2,
  .resolve 1 0 (1,2) {((1,0),true),((1,1),true),((1,3),true),((3,2),false)},
  .pigeon 2,
  .hole 2 3 2,
  .resolve 1 0 (2,2) {((2,0),true),((2,1),true),((2,3),true),((3,2),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,1),true),((2,3),true),((3,2),false)},
  .resolve 5 0 (1,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,2),false)},
  .resolve 9 0 (3,2) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,1),true),((4,3),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 2,
  .resolve 1 0 (2,2) {((1,2),false),((2,0),true),((2,1),true),((2,3),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,2),false),((2,1),true),((2,3),true),((3,0),false)},
  .resolve 5 0 (1,2) {((1,0),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,1),true),((4,3),false)},
  .hole 2 4 3,
  .resolve 1 0 (2,3) {((1,1),true),((1,3),true),((2,1),true),((3,1),true),((4,3),false)},
  .hole 1 4 3,
  .resolve 1 0 (1,3) {((1,1),true),((2,1),true),((3,1),true),((4,3),false)},
  .resolve 27 0 (4,3) {((1,1),true),((2,1),true),((3,1),true),((4,0),true),((4,1),true),((4,2),true)},
  .pigeon 3,
  .pigeon 1,
  .hole 1 3 3,
  .resolve 1 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((3,3),false)},
  .pigeon 2,
  .hole 2 3 3,
  .resolve 1 0 (2,3) {((2,0),true),((2,1),true),((2,2),true),((3,3),false)},
  .hole 1 2 0,
  .resolve 1 0 (2,0) {((1,0),false),((2,1),true),((2,2),true),((3,3),false)},
  .resolve 5 0 (1,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,3),false)},
  .resolve 9 0 (3,3) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((3,2),true)},
  .hole 3 4 2,
  .resolve 1 0 (3,2) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((4,2),false)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 3,
  .resolve 1 0 (2,3) {((1,3),false),((2,0),true),((2,1),true),((2,2),true)},
  .hole 2 3 0,
  .resolve 1 0 (2,0) {((1,3),false),((2,1),true),((2,2),true),((3,0),false)},
  .resolve 5 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)},
  .hole 1 3 0,
  .resolve 1 0 (1,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)},
  .resolve 9 0 (3,0) {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,1),true),((4,2),false)},
  .hole 2 4 2,
  .resolve 1 0 (2,2) {((1,1),true),((1,2),true),((2,1),true),((3,1),true),((4,2),false)},
  .hole 1 4 2,
  .resolve 1 0 (1,2) {((1,1),true),((2,1),true),((3,1),true),((4,2),false)},
  .resolve 27 0 (4,2) {((1,1),true),((2,1),true),((3,1),true),((4,0),true),((4,1),true)},
  .hole 0 4 1,
  .resolve 1 0 (4,1) {((0,1),false),((1,1),true),((2,1),true),((3,1),true),((4,0),true)},
  .pigeon 1,
  .pigeon 2,
  .hole 1 2 3,
  .resolve 1 0 (2,3) {((1,3),false),((2,0),true),((2,1),true),((2,2),true)},
  .pigeon 3,
  .hole 1 3 3,
  .resolve 1 0 (3,3) {((1,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .hole 2 3 2,
  .resolve 1 0 (3,2) {((1,3),false),((2,2),false),((3,0),true),((3,1),true)},
  .resolve 5 0 (2,2) {((1,3),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true)},
  .resolve 9 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((2,1),true),((3,0),true),((3,1),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 3,
  .resolve 1 0 (3,3) {((2,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .hole 1 3 2,
  .resolve 1 0 (3,2) {((1,2),false),((2,3),false),((3,0),true),((3,1),true)},
  .resolve 5 0 (2,3) {((1,2),false),((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true)},
  .hole 1 2 2,
  .resolve 1 0 (2,2) {((1,2),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true)},
  .resolve 9 0 (1,2) {((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,0),true),((3,1),true)},
  .hole 3 4 0,
  .resolve 1 0 (3,0) {((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,1),true),((4,0),false)},
  .hole 2 4 0,
  .resolve 1 0 (2,0) {((1,0),true),((1,1),true),((2,1),true),((3,1),true),((4,0),false)},
  .hole 1 4 0,
  .resolve 1 0 (1,0) {((1,1),true),((2,1),true),((3,1),true),((4,0),false)},
  .resolve 27 0 (4,0) {((0,1),false),((1,1),true),((2,1),true),((3,1),true)},
  .hole 0 3 1,
  .resolve 1 0 (3,1) {((0,1),false),((1,1),true),((2,1),true)},
  .hole 0 2 1,
  .resolve 1 0 (2,1) {((0,1),false),((1,1),true)},
  .hole 0 1 1,
  .resolve 1 0 (1,1) {((0,1),false)},
  .resolve 93 0 (0,1) {((0,0),true)},
  .pigeon 1,
  .pigeon 4,
  .hole 1 4 3,
  .resolve 1 0 (4,3) {((1,3),false),((4,0),true),((4,1),true),((4,2),true)},
  .pigeon 2,
  .hole 2 4 2,
  .resolve 1 0 (2,2) {((2,0),true),((2,1),true),((2,3),true),((4,2),false)},
  .pigeon 3,
  .hole 3 4 2,
  .resolve 1 0 (3,2) {((3,0),true),((3,1),true),((3,3),true),((4,2),false)},
  .hole 2 3 1,
  .resolve 1 0 (3,1) {((2,1),false),((3,0),true),((3,3),true),((4,2),false)},
  .resolve 5 0 (2,1) {((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,2),false)},
  .resolve 9 0 (4,2) {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,0),true),((4,1),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 2,
  .resolve 1 0 (3,2) {((2,2),false),((3,0),true),((3,1),true),((3,3),true)},
  .hole 3 4 1,
  .resolve 1 0 (3,1) {((2,2),false),((3,0),true),((3,3),true),((4,1),false)},
  .resolve 5 0 (2,2) {((2,0),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)},
  .hole 2 4 1,
  .resolve 1 0 (2,1) {((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)},
  .resolve 9 0 (4,1) {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,0),true)},
  .hole 1 3 3,
  .resolve 1 0 (3,3) {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((4,0),true)},
  .hole 1 2 3,
  .resolve 1 0 (2,3) {((1,3),false),((2,0),true),((3,0),true),((4,0),true)},
  .resolve 27 0 (1,3) {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((3,0),true),((4,0),true)},
  .pigeon 4,
  .pigeon 2,
  .hole 2 4 3,
  .resolve 1 0 (2,3) {((2,0),true),((2,1),true),((2,2),true),((4,3),false)},
  .pigeon 3,
  .hole 3 4 3,
  .resolve 1 0 (3,3) {((3,0),true),((3,1),true),((3,2),true),((4,3),false)},
  .hole 2 3 1,
  .resolve 1 0 (3,1) {((2,1),false),((3,0),true),((3,2),true),((4,3),false)},
  .resolve 5 0 (2,1) {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,3),false)},
  .resolve 9 0 (4,3) {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true),((4,1),true),((4,2),true)},
  .hole 1 4 2,
  .resolve 1 0 (4,2) {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true),((4,1),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 3,
  .resolve 1 0 (3,3) {((2,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .hole 3 4 1,
  .resolve 1 0 (3,1) {((2,3),false),((3,0),true),((3,2),true),((4,1),false)},
  .resolve 5 0 (2,3) {((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)},
  .hole 2 4 1,
  .resolve 1 0 (2,1) {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)},
  .resolve 9 0 (4,1) {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true)},
  .hole 1 3 2,
  .resolve 1 0 (3,2) {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((4,0),true)},
  .hole 1 2 2,
  .resolve 1 0 (2,2) {((1,2),false),((2,0),true),((3,0),true),((4,0),true)},
  .resolve 27 0 (1,2) {((1,0),true),((1,1),true),((2,0),true),((3,0),true),((4,0),true)},
  .pigeon 2,
  .pigeon 3,
  .hole 2 3 3,
  .resolve 1 0 (3,3) {((2,3),false),((3,0),true),((3,1),true),((3,2),true)},
  .pigeon 4,
  .hole 2 4 3,
  .resolve 1 0 (4,3) {((2,3),false),((4,0),true),((4,1),true),((4,2),true)},
  .hole 3 4 2,
  .resolve 1 0 (4,2) {((2,3),false),((3,2),false),((4,0),true),((4,1),true)},
  .resolve 5 0 (3,2) {((2,3),false),((3,0),true),((3,1),true),((4,0),true),((4,1),true)},
  .resolve 9 0 (2,3) {((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((4,0),true),((4,1),true)},
  .pigeon 3,
  .pigeon 4,
  .hole 3 4 3,
  .resolve 1 0 (4,3) {((3,3),false),((4,0),true),((4,1),true),((4,2),true)},
  .hole 2 4 2,
  .resolve 1 0 (4,2) {((2,2),false),((3,3),false),((4,0),true),((4,1),true)},
  .resolve 5 0 (3,3) {((2,2),false),((3,0),true),((3,1),true),((3,2),true),((4,0),true),((4,1),true)},
  .hole 2 3 2,
  .resolve 1 0 (3,2) {((2,2),false),((3,0),true),((3,1),true),((4,0),true),((4,1),true)},
  .resolve 9 0 (2,2) {((2,0),true),((2,1),true),((3,0),true),((3,1),true),((4,0),true),((4,1),true)},
  .hole 1 4 1,
  .resolve 1 0 (4,1) {((1,1),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true),((4,0),true)},
  .hole 1 3 1,
  .resolve 1 0 (3,1) {((1,1),false),((2,0),true),((2,1),true),((3,0),true),((4,0),true)},
  .hole 1 2 1,
  .resolve 1 0 (2,1) {((1,1),false),((2,0),true),((3,0),true),((4,0),true)},
  .resolve 27 0 (1,1) {((1,0),true),((2,0),true),((3,0),true),((4,0),true)},
  .hole 0 4 0,
  .resolve 1 0 (4,0) {((0,0),false),((1,0),true),((2,0),true),((3,0),true)},
  .hole 0 3 0,
  .resolve 1 0 (3,0) {((0,0),false),((1,0),true),((2,0),true)},
  .hole 0 2 0,
  .resolve 1 0 (2,0) {((0,0),false),((1,0),true)},
  .hole 0 1 0,
  .resolve 1 0 (1,0) {((0,0),false)},
  .resolve 93 0 (0,0) ∅]

private theorem checks : verify steps [] = true := by decide +kernel

private def proofLines : List Cl := (steps.map Step.line).reverse

private theorem derives : IsDerivation (PHP 5 4) proofLines := by
  simpa [proofLines] using verifySound steps [] .nil checks

theorem _root_.Row169.refutation377 :
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)),
      PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 377 :=
  ⟨proofLines,⟨derives,by decide +kernel⟩,by decide +kernel⟩

section Tree
variable (P : Cl → ℕ → Prop)
variable (leaf : ∀ C ∈ PHP 5 4, P C 1)
variable (fork : ∀ {A B R : Cl} {l r : ℕ}, P A l → P B r → IsResolvent A B R → P R (l+r))

private def c0 : Cl := (Step.pigeon 0).line
include leaf in
private theorem tree0 : P c0 1 := leaf _ (.inl ⟨0,rfl⟩)

private def c1 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree1 : P c1 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c2 : Cl := (Step.hole 0 4 3).line
include leaf in
private theorem tree2 : P c2 1 := leaf _ (.inr ⟨0,4,3,by decide,rfl⟩)

private def c3 : Cl := {((0,3),false),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree3 : P c3 2 := fork (tree1 P leaf) (tree2 P leaf) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c4 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree4 : P c4 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c5 : Cl := (Step.hole 3 4 2).line
include leaf in
private theorem tree5 : P c5 1 := leaf _ (.inr ⟨3,4,2,by decide,rfl⟩)

private def c6 : Cl := {((3,0),true),((3,1),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree6 : P c6 2 := fork (tree4 P leaf) (tree5 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c7 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree7 : P c7 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c8 : Cl := (Step.hole 1 3 1).line
include leaf in
private theorem tree8 : P c8 1 := leaf _ (.inr ⟨1,3,1,by decide,rfl⟩)

private def c9 : Cl := {((1,0),true),((1,2),true),((1,3),true),((3,1),false)}
include leaf fork in
private theorem tree9 : P c9 2 := fork (tree7 P leaf) (tree8 P leaf) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c10 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree10 : P c10 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c11 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree11 : P c11 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c12 : Cl := {((2,0),true),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree12 : P c12 2 := fork (tree10 P leaf) (tree11 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c13 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree13 : P c13 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c14 : Cl := {((1,0),false),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree14 : P c14 3 := fork (tree12 P leaf fork) (tree13 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c15 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree15 : P c15 5 := fork (tree9 P leaf fork) (tree14 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c16 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree16 : P c16 7 := fork (tree6 P leaf fork) (tree15 P leaf fork) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c17 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree17 : P c17 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c18 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree18 : P c18 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c19 : Cl := (Step.hole 1 2 1).line
include leaf in
private theorem tree19 : P c19 1 := leaf _ (.inr ⟨1,2,1,by decide,rfl⟩)

private def c20 : Cl := {((1,1),false),((2,0),true),((2,2),true),((2,3),true)}
include leaf fork in
private theorem tree20 : P c20 2 := fork (tree18 P leaf) (tree19 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c21 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree21 : P c21 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c22 : Cl := {((1,1),false),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree22 : P c22 3 := fork (tree20 P leaf fork) (tree21 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c23 : Cl := {((1,0),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree23 : P c23 4 := fork (tree17 P leaf) (tree22 P leaf fork) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c24 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree24 : P c24 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c25 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree25 : P c25 5 := fork (tree23 P leaf fork) (tree24 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c26 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree26 : P c26 12 := fork (tree16 P leaf fork) (tree25 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c27 : Cl := (Step.hole 2 4 2).line
include leaf in
private theorem tree27 : P c27 1 := leaf _ (.inr ⟨2,4,2,by decide,rfl⟩)

private def c28 : Cl := {((1,2),true),((1,3),true),((2,3),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree28 : P c28 13 := fork (tree26 P leaf fork) (tree27 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c29 : Cl := (Step.hole 1 4 2).line
include leaf in
private theorem tree29 : P c29 1 := leaf _ (.inr ⟨1,4,2,by decide,rfl⟩)

private def c30 : Cl := {((1,3),true),((2,3),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree30 : P c30 14 := fork (tree28 P leaf fork) (tree29 P leaf) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c31 : Cl := {((0,3),false),((1,3),true),((2,3),true),((3,3),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree31 : P c31 16 := fork (tree3 P leaf fork) (tree30 P leaf fork) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c32 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree32 : P c32 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c33 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree33 : P c33 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c34 : Cl := (Step.hole 1 3 2).line
include leaf in
private theorem tree34 : P c34 1 := leaf _ (.inr ⟨1,3,2,by decide,rfl⟩)

private def c35 : Cl := {((1,0),true),((1,1),true),((1,3),true),((3,2),false)}
include leaf fork in
private theorem tree35 : P c35 2 := fork (tree33 P leaf) (tree34 P leaf) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c36 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree36 : P c36 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c37 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree37 : P c37 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c38 : Cl := {((2,0),true),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree38 : P c38 2 := fork (tree36 P leaf) (tree37 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c39 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree39 : P c39 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c40 : Cl := {((1,0),false),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree40 : P c40 3 := fork (tree38 P leaf fork) (tree39 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c41 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree41 : P c41 5 := fork (tree35 P leaf fork) (tree40 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c42 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,1),true),((3,3),true)}
include leaf fork in
private theorem tree42 : P c42 6 := fork (tree32 P leaf) (tree41 P leaf fork) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c43 : Cl := (Step.hole 3 4 1).line
include leaf in
private theorem tree43 : P c43 1 := leaf _ (.inr ⟨3,4,1,by decide,rfl⟩)

private def c44 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree44 : P c44 7 := fork (tree42 P leaf fork) (tree43 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c45 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree45 : P c45 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c46 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree46 : P c46 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c47 : Cl := (Step.hole 1 2 2).line
include leaf in
private theorem tree47 : P c47 1 := leaf _ (.inr ⟨1,2,2,by decide,rfl⟩)

private def c48 : Cl := {((1,2),false),((2,0),true),((2,1),true),((2,3),true)}
include leaf fork in
private theorem tree48 : P c48 2 := fork (tree46 P leaf) (tree47 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c49 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree49 : P c49 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c50 : Cl := {((1,2),false),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree50 : P c50 3 := fork (tree48 P leaf fork) (tree49 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c51 : Cl := {((1,0),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree51 : P c51 4 := fork (tree45 P leaf) (tree50 P leaf fork) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c52 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree52 : P c52 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c53 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree53 : P c53 5 := fork (tree51 P leaf fork) (tree52 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c54 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree54 : P c54 12 := fork (tree44 P leaf fork) (tree53 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c55 : Cl := (Step.hole 2 4 1).line
include leaf in
private theorem tree55 : P c55 1 := leaf _ (.inr ⟨2,4,1,by decide,rfl⟩)

private def c56 : Cl := {((1,1),true),((1,3),true),((2,3),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree56 : P c56 13 := fork (tree54 P leaf fork) (tree55 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c57 : Cl := (Step.hole 1 4 1).line
include leaf in
private theorem tree57 : P c57 1 := leaf _ (.inr ⟨1,4,1,by decide,rfl⟩)

private def c58 : Cl := {((1,3),true),((2,3),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree58 : P c58 14 := fork (tree56 P leaf fork) (tree57 P leaf) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c59 : Cl := {((0,3),false),((1,3),true),((2,3),true),((3,3),true),((4,0),true)}
include leaf fork in
private theorem tree59 : P c59 30 := fork (tree31 P leaf fork) (tree58 P leaf fork) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c60 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree60 : P c60 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c61 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree61 : P c61 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c62 : Cl := (Step.hole 1 2 2).line
include leaf in
private theorem tree62 : P c62 1 := leaf _ (.inr ⟨1,2,2,by decide,rfl⟩)

private def c63 : Cl := {((1,2),false),((2,0),true),((2,1),true),((2,3),true)}
include leaf fork in
private theorem tree63 : P c63 2 := fork (tree61 P leaf) (tree62 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c64 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree64 : P c64 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c65 : Cl := (Step.hole 1 3 2).line
include leaf in
private theorem tree65 : P c65 1 := leaf _ (.inr ⟨1,3,2,by decide,rfl⟩)

private def c66 : Cl := {((1,2),false),((3,0),true),((3,1),true),((3,3),true)}
include leaf fork in
private theorem tree66 : P c66 2 := fork (tree64 P leaf) (tree65 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c67 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree67 : P c67 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c68 : Cl := {((1,2),false),((2,1),false),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree68 : P c68 3 := fork (tree66 P leaf fork) (tree67 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c69 : Cl := {((1,2),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree69 : P c69 5 := fork (tree63 P leaf fork) (tree68 P leaf fork) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c70 : Cl := {((1,0),true),((1,1),true),((1,3),true),((2,0),true),((2,3),true),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree70 : P c70 6 := fork (tree60 P leaf) (tree69 P leaf fork) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c71 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree71 : P c71 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c72 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree72 : P c72 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c73 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree73 : P c73 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c74 : Cl := {((2,2),false),((3,0),true),((3,1),true),((3,3),true)}
include leaf fork in
private theorem tree74 : P c74 2 := fork (tree72 P leaf) (tree73 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c75 : Cl := (Step.hole 1 3 1).line
include leaf in
private theorem tree75 : P c75 1 := leaf _ (.inr ⟨1,3,1,by decide,rfl⟩)

private def c76 : Cl := {((1,1),false),((2,2),false),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree76 : P c76 3 := fork (tree74 P leaf fork) (tree75 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c77 : Cl := {((1,1),false),((2,0),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree77 : P c77 4 := fork (tree71 P leaf) (tree76 P leaf fork) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c78 : Cl := (Step.hole 1 2 1).line
include leaf in
private theorem tree78 : P c78 1 := leaf _ (.inr ⟨1,2,1,by decide,rfl⟩)

private def c79 : Cl := {((1,1),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree79 : P c79 5 := fork (tree77 P leaf fork) (tree78 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c80 : Cl := {((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,0),true),((3,3),true)}
include leaf fork in
private theorem tree80 : P c80 11 := fork (tree70 P leaf fork) (tree79 P leaf fork) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c81 : Cl := (Step.hole 3 4 0).line
include leaf in
private theorem tree81 : P c81 1 := leaf _ (.inr ⟨3,4,0,by decide,rfl⟩)

private def c82 : Cl := {((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,3),true),((4,0),false)}
include leaf fork in
private theorem tree82 : P c82 12 := fork (tree80 P leaf fork) (tree81 P leaf) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c83 : Cl := (Step.hole 2 4 0).line
include leaf in
private theorem tree83 : P c83 1 := leaf _ (.inr ⟨2,4,0,by decide,rfl⟩)

private def c84 : Cl := {((1,0),true),((1,3),true),((2,3),true),((3,3),true),((4,0),false)}
include leaf fork in
private theorem tree84 : P c84 13 := fork (tree82 P leaf fork) (tree83 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c85 : Cl := (Step.hole 1 4 0).line
include leaf in
private theorem tree85 : P c85 1 := leaf _ (.inr ⟨1,4,0,by decide,rfl⟩)

private def c86 : Cl := {((1,3),true),((2,3),true),((3,3),true),((4,0),false)}
include leaf fork in
private theorem tree86 : P c86 14 := fork (tree84 P leaf fork) (tree85 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c87 : Cl := {((0,3),false),((1,3),true),((2,3),true),((3,3),true)}
include leaf fork in
private theorem tree87 : P c87 44 := fork (tree59 P leaf fork) (tree86 P leaf fork) ⟨(4,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c88 : Cl := (Step.hole 0 3 3).line
include leaf in
private theorem tree88 : P c88 1 := leaf _ (.inr ⟨0,3,3,by decide,rfl⟩)

private def c89 : Cl := {((0,3),false),((1,3),true),((2,3),true)}
include leaf fork in
private theorem tree89 : P c89 45 := fork (tree87 P leaf fork) (tree88 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c90 : Cl := (Step.hole 0 2 3).line
include leaf in
private theorem tree90 : P c90 1 := leaf _ (.inr ⟨0,2,3,by decide,rfl⟩)

private def c91 : Cl := {((0,3),false),((1,3),true)}
include leaf fork in
private theorem tree91 : P c91 46 := fork (tree89 P leaf fork) (tree90 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c92 : Cl := (Step.hole 0 1 3).line
include leaf in
private theorem tree92 : P c92 1 := leaf _ (.inr ⟨0,1,3,by decide,rfl⟩)

private def c93 : Cl := {((0,3),false)}
include leaf fork in
private theorem tree93 : P c93 47 := fork (tree91 P leaf fork) (tree92 P leaf) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c94 : Cl := {((0,0),true),((0,1),true),((0,2),true)}
include leaf fork in
private theorem tree94 : P c94 48 := fork (tree0 P leaf) (tree93 P leaf fork) ⟨(0,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c95 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree95 : P c95 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c96 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree96 : P c96 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c97 : Cl := (Step.hole 3 4 3).line
include leaf in
private theorem tree97 : P c97 1 := leaf _ (.inr ⟨3,4,3,by decide,rfl⟩)

private def c98 : Cl := {((3,0),true),((3,1),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree98 : P c98 2 := fork (tree96 P leaf) (tree97 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c99 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree99 : P c99 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c100 : Cl := (Step.hole 1 3 1).line
include leaf in
private theorem tree100 : P c100 1 := leaf _ (.inr ⟨1,3,1,by decide,rfl⟩)

private def c101 : Cl := {((1,0),true),((1,2),true),((1,3),true),((3,1),false)}
include leaf fork in
private theorem tree101 : P c101 2 := fork (tree99 P leaf) (tree100 P leaf) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c102 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree102 : P c102 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c103 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree103 : P c103 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c104 : Cl := {((2,0),true),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree104 : P c104 2 := fork (tree102 P leaf) (tree103 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c105 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree105 : P c105 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c106 : Cl := {((1,0),false),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree106 : P c106 3 := fork (tree104 P leaf fork) (tree105 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c107 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,1),false)}
include leaf fork in
private theorem tree107 : P c107 5 := fork (tree101 P leaf fork) (tree106 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c108 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree108 : P c108 7 := fork (tree98 P leaf fork) (tree107 P leaf fork) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c109 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree109 : P c109 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c110 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree110 : P c110 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c111 : Cl := (Step.hole 1 2 1).line
include leaf in
private theorem tree111 : P c111 1 := leaf _ (.inr ⟨1,2,1,by decide,rfl⟩)

private def c112 : Cl := {((1,1),false),((2,0),true),((2,2),true),((2,3),true)}
include leaf fork in
private theorem tree112 : P c112 2 := fork (tree110 P leaf) (tree111 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c113 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree113 : P c113 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c114 : Cl := {((1,1),false),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree114 : P c114 3 := fork (tree112 P leaf fork) (tree113 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c115 : Cl := {((1,0),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree115 : P c115 4 := fork (tree109 P leaf) (tree114 P leaf fork) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c116 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree116 : P c116 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c117 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree117 : P c117 5 := fork (tree115 P leaf fork) (tree116 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c118 : Cl := {((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree118 : P c118 12 := fork (tree108 P leaf fork) (tree117 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c119 : Cl := (Step.hole 2 4 3).line
include leaf in
private theorem tree119 : P c119 1 := leaf _ (.inr ⟨2,4,3,by decide,rfl⟩)

private def c120 : Cl := {((1,2),true),((1,3),true),((2,2),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree120 : P c120 13 := fork (tree118 P leaf fork) (tree119 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c121 : Cl := (Step.hole 1 4 3).line
include leaf in
private theorem tree121 : P c121 1 := leaf _ (.inr ⟨1,4,3,by decide,rfl⟩)

private def c122 : Cl := {((1,2),true),((2,2),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree122 : P c122 14 := fork (tree120 P leaf fork) (tree121 P leaf) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c123 : Cl := {((1,2),true),((2,2),true),((3,2),true),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree123 : P c123 15 := fork (tree95 P leaf) (tree122 P leaf fork) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c124 : Cl := (Step.hole 0 4 2).line
include leaf in
private theorem tree124 : P c124 1 := leaf _ (.inr ⟨0,4,2,by decide,rfl⟩)

private def c125 : Cl := {((0,2),false),((1,2),true),((2,2),true),((3,2),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree125 : P c125 16 := fork (tree123 P leaf fork) (tree124 P leaf) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c126 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree126 : P c126 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c127 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree127 : P c127 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c128 : Cl := (Step.hole 1 3 3).line
include leaf in
private theorem tree128 : P c128 1 := leaf _ (.inr ⟨1,3,3,by decide,rfl⟩)

private def c129 : Cl := {((1,0),true),((1,1),true),((1,2),true),((3,3),false)}
include leaf fork in
private theorem tree129 : P c129 2 := fork (tree127 P leaf) (tree128 P leaf) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c130 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree130 : P c130 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c131 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree131 : P c131 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c132 : Cl := {((2,0),true),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree132 : P c132 2 := fork (tree130 P leaf) (tree131 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c133 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree133 : P c133 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c134 : Cl := {((1,0),false),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree134 : P c134 3 := fork (tree132 P leaf fork) (tree133 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c135 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree135 : P c135 5 := fork (tree129 P leaf fork) (tree134 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c136 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree136 : P c136 6 := fork (tree126 P leaf) (tree135 P leaf fork) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c137 : Cl := (Step.hole 3 4 1).line
include leaf in
private theorem tree137 : P c137 1 := leaf _ (.inr ⟨3,4,1,by decide,rfl⟩)

private def c138 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree138 : P c138 7 := fork (tree136 P leaf fork) (tree137 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c139 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree139 : P c139 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c140 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree140 : P c140 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c141 : Cl := (Step.hole 1 2 3).line
include leaf in
private theorem tree141 : P c141 1 := leaf _ (.inr ⟨1,2,3,by decide,rfl⟩)

private def c142 : Cl := {((1,3),false),((2,0),true),((2,1),true),((2,2),true)}
include leaf fork in
private theorem tree142 : P c142 2 := fork (tree140 P leaf) (tree141 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c143 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree143 : P c143 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c144 : Cl := {((1,3),false),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree144 : P c144 3 := fork (tree142 P leaf fork) (tree143 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c145 : Cl := {((1,0),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree145 : P c145 4 := fork (tree139 P leaf) (tree144 P leaf fork) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c146 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree146 : P c146 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c147 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree147 : P c147 5 := fork (tree145 P leaf fork) (tree146 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c148 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree148 : P c148 12 := fork (tree138 P leaf fork) (tree147 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c149 : Cl := (Step.hole 2 4 1).line
include leaf in
private theorem tree149 : P c149 1 := leaf _ (.inr ⟨2,4,1,by decide,rfl⟩)

private def c150 : Cl := {((1,1),true),((1,2),true),((2,2),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree150 : P c150 13 := fork (tree148 P leaf fork) (tree149 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c151 : Cl := (Step.hole 1 4 1).line
include leaf in
private theorem tree151 : P c151 1 := leaf _ (.inr ⟨1,4,1,by decide,rfl⟩)

private def c152 : Cl := {((1,2),true),((2,2),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree152 : P c152 14 := fork (tree150 P leaf fork) (tree151 P leaf) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c153 : Cl := {((0,2),false),((1,2),true),((2,2),true),((3,2),true),((4,0),true)}
include leaf fork in
private theorem tree153 : P c153 30 := fork (tree125 P leaf fork) (tree152 P leaf fork) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c154 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree154 : P c154 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c155 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree155 : P c155 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c156 : Cl := (Step.hole 1 2 3).line
include leaf in
private theorem tree156 : P c156 1 := leaf _ (.inr ⟨1,2,3,by decide,rfl⟩)

private def c157 : Cl := {((1,3),false),((2,0),true),((2,1),true),((2,2),true)}
include leaf fork in
private theorem tree157 : P c157 2 := fork (tree155 P leaf) (tree156 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c158 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree158 : P c158 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c159 : Cl := (Step.hole 1 3 3).line
include leaf in
private theorem tree159 : P c159 1 := leaf _ (.inr ⟨1,3,3,by decide,rfl⟩)

private def c160 : Cl := {((1,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree160 : P c160 2 := fork (tree158 P leaf) (tree159 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c161 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree161 : P c161 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c162 : Cl := {((1,3),false),((2,1),false),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree162 : P c162 3 := fork (tree160 P leaf fork) (tree161 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c163 : Cl := {((1,3),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree163 : P c163 5 := fork (tree157 P leaf fork) (tree162 P leaf fork) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c164 : Cl := {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((2,2),true),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree164 : P c164 6 := fork (tree154 P leaf) (tree163 P leaf fork) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c165 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree165 : P c165 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c166 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree166 : P c166 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c167 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree167 : P c167 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c168 : Cl := {((2,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree168 : P c168 2 := fork (tree166 P leaf) (tree167 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c169 : Cl := (Step.hole 1 3 1).line
include leaf in
private theorem tree169 : P c169 1 := leaf _ (.inr ⟨1,3,1,by decide,rfl⟩)

private def c170 : Cl := {((1,1),false),((2,3),false),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree170 : P c170 3 := fork (tree168 P leaf fork) (tree169 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c171 : Cl := {((1,1),false),((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree171 : P c171 4 := fork (tree165 P leaf) (tree170 P leaf fork) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c172 : Cl := (Step.hole 1 2 1).line
include leaf in
private theorem tree172 : P c172 1 := leaf _ (.inr ⟨1,2,1,by decide,rfl⟩)

private def c173 : Cl := {((1,1),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree173 : P c173 5 := fork (tree171 P leaf fork) (tree172 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c174 : Cl := {((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,0),true),((3,2),true)}
include leaf fork in
private theorem tree174 : P c174 11 := fork (tree164 P leaf fork) (tree173 P leaf fork) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c175 : Cl := (Step.hole 3 4 0).line
include leaf in
private theorem tree175 : P c175 1 := leaf _ (.inr ⟨3,4,0,by decide,rfl⟩)

private def c176 : Cl := {((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,2),true),((4,0),false)}
include leaf fork in
private theorem tree176 : P c176 12 := fork (tree174 P leaf fork) (tree175 P leaf) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c177 : Cl := (Step.hole 2 4 0).line
include leaf in
private theorem tree177 : P c177 1 := leaf _ (.inr ⟨2,4,0,by decide,rfl⟩)

private def c178 : Cl := {((1,0),true),((1,2),true),((2,2),true),((3,2),true),((4,0),false)}
include leaf fork in
private theorem tree178 : P c178 13 := fork (tree176 P leaf fork) (tree177 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c179 : Cl := (Step.hole 1 4 0).line
include leaf in
private theorem tree179 : P c179 1 := leaf _ (.inr ⟨1,4,0,by decide,rfl⟩)

private def c180 : Cl := {((1,2),true),((2,2),true),((3,2),true),((4,0),false)}
include leaf fork in
private theorem tree180 : P c180 14 := fork (tree178 P leaf fork) (tree179 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c181 : Cl := {((0,2),false),((1,2),true),((2,2),true),((3,2),true)}
include leaf fork in
private theorem tree181 : P c181 44 := fork (tree153 P leaf fork) (tree180 P leaf fork) ⟨(4,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c182 : Cl := (Step.hole 0 3 2).line
include leaf in
private theorem tree182 : P c182 1 := leaf _ (.inr ⟨0,3,2,by decide,rfl⟩)

private def c183 : Cl := {((0,2),false),((1,2),true),((2,2),true)}
include leaf fork in
private theorem tree183 : P c183 45 := fork (tree181 P leaf fork) (tree182 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c184 : Cl := (Step.hole 0 2 2).line
include leaf in
private theorem tree184 : P c184 1 := leaf _ (.inr ⟨0,2,2,by decide,rfl⟩)

private def c185 : Cl := {((0,2),false),((1,2),true)}
include leaf fork in
private theorem tree185 : P c185 46 := fork (tree183 P leaf fork) (tree184 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c186 : Cl := (Step.hole 0 1 2).line
include leaf in
private theorem tree186 : P c186 1 := leaf _ (.inr ⟨0,1,2,by decide,rfl⟩)

private def c187 : Cl := {((0,2),false)}
include leaf fork in
private theorem tree187 : P c187 47 := fork (tree185 P leaf fork) (tree186 P leaf) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c188 : Cl := {((0,0),true),((0,1),true)}
include leaf fork in
private theorem tree188 : P c188 95 := fork (tree94 P leaf fork) (tree187 P leaf fork) ⟨(0,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c189 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree189 : P c189 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c190 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree190 : P c190 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c191 : Cl := (Step.hole 3 4 3).line
include leaf in
private theorem tree191 : P c191 1 := leaf _ (.inr ⟨3,4,3,by decide,rfl⟩)

private def c192 : Cl := {((3,0),true),((3,1),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree192 : P c192 2 := fork (tree190 P leaf) (tree191 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c193 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree193 : P c193 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c194 : Cl := (Step.hole 1 3 2).line
include leaf in
private theorem tree194 : P c194 1 := leaf _ (.inr ⟨1,3,2,by decide,rfl⟩)

private def c195 : Cl := {((1,0),true),((1,1),true),((1,3),true),((3,2),false)}
include leaf fork in
private theorem tree195 : P c195 2 := fork (tree193 P leaf) (tree194 P leaf) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c196 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree196 : P c196 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c197 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree197 : P c197 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c198 : Cl := {((2,0),true),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree198 : P c198 2 := fork (tree196 P leaf) (tree197 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c199 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree199 : P c199 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c200 : Cl := {((1,0),false),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree200 : P c200 3 := fork (tree198 P leaf fork) (tree199 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c201 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,2),false)}
include leaf fork in
private theorem tree201 : P c201 5 := fork (tree195 P leaf fork) (tree200 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c202 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),true),((3,1),true),((4,3),false)}
include leaf fork in
private theorem tree202 : P c202 7 := fork (tree192 P leaf fork) (tree201 P leaf fork) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c203 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree203 : P c203 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c204 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree204 : P c204 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c205 : Cl := (Step.hole 1 2 2).line
include leaf in
private theorem tree205 : P c205 1 := leaf _ (.inr ⟨1,2,2,by decide,rfl⟩)

private def c206 : Cl := {((1,2),false),((2,0),true),((2,1),true),((2,3),true)}
include leaf fork in
private theorem tree206 : P c206 2 := fork (tree204 P leaf) (tree205 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c207 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree207 : P c207 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c208 : Cl := {((1,2),false),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree208 : P c208 3 := fork (tree206 P leaf fork) (tree207 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c209 : Cl := {((1,0),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree209 : P c209 4 := fork (tree203 P leaf) (tree208 P leaf fork) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c210 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree210 : P c210 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c211 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,0),false)}
include leaf fork in
private theorem tree211 : P c211 5 := fork (tree209 P leaf fork) (tree210 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c212 : Cl := {((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,1),true),((4,3),false)}
include leaf fork in
private theorem tree212 : P c212 12 := fork (tree202 P leaf fork) (tree211 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c213 : Cl := (Step.hole 2 4 3).line
include leaf in
private theorem tree213 : P c213 1 := leaf _ (.inr ⟨2,4,3,by decide,rfl⟩)

private def c214 : Cl := {((1,1),true),((1,3),true),((2,1),true),((3,1),true),((4,3),false)}
include leaf fork in
private theorem tree214 : P c214 13 := fork (tree212 P leaf fork) (tree213 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c215 : Cl := (Step.hole 1 4 3).line
include leaf in
private theorem tree215 : P c215 1 := leaf _ (.inr ⟨1,4,3,by decide,rfl⟩)

private def c216 : Cl := {((1,1),true),((2,1),true),((3,1),true),((4,3),false)}
include leaf fork in
private theorem tree216 : P c216 14 := fork (tree214 P leaf fork) (tree215 P leaf) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c217 : Cl := {((1,1),true),((2,1),true),((3,1),true),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree217 : P c217 15 := fork (tree189 P leaf) (tree216 P leaf fork) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c218 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree218 : P c218 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c219 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree219 : P c219 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c220 : Cl := (Step.hole 1 3 3).line
include leaf in
private theorem tree220 : P c220 1 := leaf _ (.inr ⟨1,3,3,by decide,rfl⟩)

private def c221 : Cl := {((1,0),true),((1,1),true),((1,2),true),((3,3),false)}
include leaf fork in
private theorem tree221 : P c221 2 := fork (tree219 P leaf) (tree220 P leaf) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c222 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree222 : P c222 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c223 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree223 : P c223 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c224 : Cl := {((2,0),true),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree224 : P c224 2 := fork (tree222 P leaf) (tree223 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c225 : Cl := (Step.hole 1 2 0).line
include leaf in
private theorem tree225 : P c225 1 := leaf _ (.inr ⟨1,2,0,by decide,rfl⟩)

private def c226 : Cl := {((1,0),false),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree226 : P c226 3 := fork (tree224 P leaf fork) (tree225 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c227 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,3),false)}
include leaf fork in
private theorem tree227 : P c227 5 := fork (tree221 P leaf fork) (tree226 P leaf fork) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c228 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree228 : P c228 6 := fork (tree218 P leaf) (tree227 P leaf fork) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c229 : Cl := (Step.hole 3 4 2).line
include leaf in
private theorem tree229 : P c229 1 := leaf _ (.inr ⟨3,4,2,by decide,rfl⟩)

private def c230 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((4,2),false)}
include leaf fork in
private theorem tree230 : P c230 7 := fork (tree228 P leaf fork) (tree229 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c231 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree231 : P c231 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c232 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree232 : P c232 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c233 : Cl := (Step.hole 1 2 3).line
include leaf in
private theorem tree233 : P c233 1 := leaf _ (.inr ⟨1,2,3,by decide,rfl⟩)

private def c234 : Cl := {((1,3),false),((2,0),true),((2,1),true),((2,2),true)}
include leaf fork in
private theorem tree234 : P c234 2 := fork (tree232 P leaf) (tree233 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c235 : Cl := (Step.hole 2 3 0).line
include leaf in
private theorem tree235 : P c235 1 := leaf _ (.inr ⟨2,3,0,by decide,rfl⟩)

private def c236 : Cl := {((1,3),false),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree236 : P c236 3 := fork (tree234 P leaf fork) (tree235 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c237 : Cl := {((1,0),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree237 : P c237 4 := fork (tree231 P leaf) (tree236 P leaf fork) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c238 : Cl := (Step.hole 1 3 0).line
include leaf in
private theorem tree238 : P c238 1 := leaf _ (.inr ⟨1,3,0,by decide,rfl⟩)

private def c239 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,0),false)}
include leaf fork in
private theorem tree239 : P c239 5 := fork (tree237 P leaf fork) (tree238 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c240 : Cl := {((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,1),true),((4,2),false)}
include leaf fork in
private theorem tree240 : P c240 12 := fork (tree230 P leaf fork) (tree239 P leaf fork) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c241 : Cl := (Step.hole 2 4 2).line
include leaf in
private theorem tree241 : P c241 1 := leaf _ (.inr ⟨2,4,2,by decide,rfl⟩)

private def c242 : Cl := {((1,1),true),((1,2),true),((2,1),true),((3,1),true),((4,2),false)}
include leaf fork in
private theorem tree242 : P c242 13 := fork (tree240 P leaf fork) (tree241 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c243 : Cl := (Step.hole 1 4 2).line
include leaf in
private theorem tree243 : P c243 1 := leaf _ (.inr ⟨1,4,2,by decide,rfl⟩)

private def c244 : Cl := {((1,1),true),((2,1),true),((3,1),true),((4,2),false)}
include leaf fork in
private theorem tree244 : P c244 14 := fork (tree242 P leaf fork) (tree243 P leaf) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c245 : Cl := {((1,1),true),((2,1),true),((3,1),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree245 : P c245 29 := fork (tree217 P leaf fork) (tree244 P leaf fork) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c246 : Cl := (Step.hole 0 4 1).line
include leaf in
private theorem tree246 : P c246 1 := leaf _ (.inr ⟨0,4,1,by decide,rfl⟩)

private def c247 : Cl := {((0,1),false),((1,1),true),((2,1),true),((3,1),true),((4,0),true)}
include leaf fork in
private theorem tree247 : P c247 30 := fork (tree245 P leaf fork) (tree246 P leaf) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c248 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree248 : P c248 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c249 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree249 : P c249 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c250 : Cl := (Step.hole 1 2 3).line
include leaf in
private theorem tree250 : P c250 1 := leaf _ (.inr ⟨1,2,3,by decide,rfl⟩)

private def c251 : Cl := {((1,3),false),((2,0),true),((2,1),true),((2,2),true)}
include leaf fork in
private theorem tree251 : P c251 2 := fork (tree249 P leaf) (tree250 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c252 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree252 : P c252 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c253 : Cl := (Step.hole 1 3 3).line
include leaf in
private theorem tree253 : P c253 1 := leaf _ (.inr ⟨1,3,3,by decide,rfl⟩)

private def c254 : Cl := {((1,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree254 : P c254 2 := fork (tree252 P leaf) (tree253 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c255 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree255 : P c255 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c256 : Cl := {((1,3),false),((2,2),false),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree256 : P c256 3 := fork (tree254 P leaf fork) (tree255 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c257 : Cl := {((1,3),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree257 : P c257 5 := fork (tree251 P leaf fork) (tree256 P leaf fork) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c258 : Cl := {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((2,1),true),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree258 : P c258 6 := fork (tree248 P leaf) (tree257 P leaf fork) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c259 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree259 : P c259 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c260 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree260 : P c260 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c261 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree261 : P c261 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c262 : Cl := {((2,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree262 : P c262 2 := fork (tree260 P leaf) (tree261 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c263 : Cl := (Step.hole 1 3 2).line
include leaf in
private theorem tree263 : P c263 1 := leaf _ (.inr ⟨1,3,2,by decide,rfl⟩)

private def c264 : Cl := {((1,2),false),((2,3),false),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree264 : P c264 3 := fork (tree262 P leaf fork) (tree263 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c265 : Cl := {((1,2),false),((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree265 : P c265 4 := fork (tree259 P leaf) (tree264 P leaf fork) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c266 : Cl := (Step.hole 1 2 2).line
include leaf in
private theorem tree266 : P c266 1 := leaf _ (.inr ⟨1,2,2,by decide,rfl⟩)

private def c267 : Cl := {((1,2),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree267 : P c267 5 := fork (tree265 P leaf fork) (tree266 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c268 : Cl := {((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,0),true),((3,1),true)}
include leaf fork in
private theorem tree268 : P c268 11 := fork (tree258 P leaf fork) (tree267 P leaf fork) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c269 : Cl := (Step.hole 3 4 0).line
include leaf in
private theorem tree269 : P c269 1 := leaf _ (.inr ⟨3,4,0,by decide,rfl⟩)

private def c270 : Cl := {((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,1),true),((4,0),false)}
include leaf fork in
private theorem tree270 : P c270 12 := fork (tree268 P leaf fork) (tree269 P leaf) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c271 : Cl := (Step.hole 2 4 0).line
include leaf in
private theorem tree271 : P c271 1 := leaf _ (.inr ⟨2,4,0,by decide,rfl⟩)

private def c272 : Cl := {((1,0),true),((1,1),true),((2,1),true),((3,1),true),((4,0),false)}
include leaf fork in
private theorem tree272 : P c272 13 := fork (tree270 P leaf fork) (tree271 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c273 : Cl := (Step.hole 1 4 0).line
include leaf in
private theorem tree273 : P c273 1 := leaf _ (.inr ⟨1,4,0,by decide,rfl⟩)

private def c274 : Cl := {((1,1),true),((2,1),true),((3,1),true),((4,0),false)}
include leaf fork in
private theorem tree274 : P c274 14 := fork (tree272 P leaf fork) (tree273 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c275 : Cl := {((0,1),false),((1,1),true),((2,1),true),((3,1),true)}
include leaf fork in
private theorem tree275 : P c275 44 := fork (tree247 P leaf fork) (tree274 P leaf fork) ⟨(4,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c276 : Cl := (Step.hole 0 3 1).line
include leaf in
private theorem tree276 : P c276 1 := leaf _ (.inr ⟨0,3,1,by decide,rfl⟩)

private def c277 : Cl := {((0,1),false),((1,1),true),((2,1),true)}
include leaf fork in
private theorem tree277 : P c277 45 := fork (tree275 P leaf fork) (tree276 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c278 : Cl := (Step.hole 0 2 1).line
include leaf in
private theorem tree278 : P c278 1 := leaf _ (.inr ⟨0,2,1,by decide,rfl⟩)

private def c279 : Cl := {((0,1),false),((1,1),true)}
include leaf fork in
private theorem tree279 : P c279 46 := fork (tree277 P leaf fork) (tree278 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c280 : Cl := (Step.hole 0 1 1).line
include leaf in
private theorem tree280 : P c280 1 := leaf _ (.inr ⟨0,1,1,by decide,rfl⟩)

private def c281 : Cl := {((0,1),false)}
include leaf fork in
private theorem tree281 : P c281 47 := fork (tree279 P leaf fork) (tree280 P leaf) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c282 : Cl := {((0,0),true)}
include leaf fork in
private theorem tree282 : P c282 142 := fork (tree188 P leaf fork) (tree281 P leaf fork) ⟨(0,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c283 : Cl := (Step.pigeon 1).line
include leaf in
private theorem tree283 : P c283 1 := leaf _ (.inl ⟨1,rfl⟩)

private def c284 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree284 : P c284 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c285 : Cl := (Step.hole 1 4 3).line
include leaf in
private theorem tree285 : P c285 1 := leaf _ (.inr ⟨1,4,3,by decide,rfl⟩)

private def c286 : Cl := {((1,3),false),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree286 : P c286 2 := fork (tree284 P leaf) (tree285 P leaf) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c287 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree287 : P c287 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c288 : Cl := (Step.hole 2 4 2).line
include leaf in
private theorem tree288 : P c288 1 := leaf _ (.inr ⟨2,4,2,by decide,rfl⟩)

private def c289 : Cl := {((2,0),true),((2,1),true),((2,3),true),((4,2),false)}
include leaf fork in
private theorem tree289 : P c289 2 := fork (tree287 P leaf) (tree288 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c290 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree290 : P c290 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c291 : Cl := (Step.hole 3 4 2).line
include leaf in
private theorem tree291 : P c291 1 := leaf _ (.inr ⟨3,4,2,by decide,rfl⟩)

private def c292 : Cl := {((3,0),true),((3,1),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree292 : P c292 2 := fork (tree290 P leaf) (tree291 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c293 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree293 : P c293 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c294 : Cl := {((2,1),false),((3,0),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree294 : P c294 3 := fork (tree292 P leaf fork) (tree293 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c295 : Cl := {((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,2),false)}
include leaf fork in
private theorem tree295 : P c295 5 := fork (tree289 P leaf fork) (tree294 P leaf fork) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c296 : Cl := {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree296 : P c296 7 := fork (tree286 P leaf fork) (tree295 P leaf fork) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c297 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree297 : P c297 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c298 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree298 : P c298 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c299 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree299 : P c299 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c300 : Cl := {((2,2),false),((3,0),true),((3,1),true),((3,3),true)}
include leaf fork in
private theorem tree300 : P c300 2 := fork (tree298 P leaf) (tree299 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c301 : Cl := (Step.hole 3 4 1).line
include leaf in
private theorem tree301 : P c301 1 := leaf _ (.inr ⟨3,4,1,by decide,rfl⟩)

private def c302 : Cl := {((2,2),false),((3,0),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree302 : P c302 3 := fork (tree300 P leaf fork) (tree301 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c303 : Cl := {((2,0),true),((2,1),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree303 : P c303 4 := fork (tree297 P leaf) (tree302 P leaf fork) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c304 : Cl := (Step.hole 2 4 1).line
include leaf in
private theorem tree304 : P c304 1 := leaf _ (.inr ⟨2,4,1,by decide,rfl⟩)

private def c305 : Cl := {((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,1),false)}
include leaf fork in
private theorem tree305 : P c305 5 := fork (tree303 P leaf fork) (tree304 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c306 : Cl := {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((3,3),true),((4,0),true)}
include leaf fork in
private theorem tree306 : P c306 12 := fork (tree296 P leaf fork) (tree305 P leaf fork) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c307 : Cl := (Step.hole 1 3 3).line
include leaf in
private theorem tree307 : P c307 1 := leaf _ (.inr ⟨1,3,3,by decide,rfl⟩)

private def c308 : Cl := {((1,3),false),((2,0),true),((2,3),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree308 : P c308 13 := fork (tree306 P leaf fork) (tree307 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c309 : Cl := (Step.hole 1 2 3).line
include leaf in
private theorem tree309 : P c309 1 := leaf _ (.inr ⟨1,2,3,by decide,rfl⟩)

private def c310 : Cl := {((1,3),false),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree310 : P c310 14 := fork (tree308 P leaf fork) (tree309 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c311 : Cl := {((1,0),true),((1,1),true),((1,2),true),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree311 : P c311 15 := fork (tree283 P leaf) (tree310 P leaf fork) ⟨(1,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c312 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree312 : P c312 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c313 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree313 : P c313 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c314 : Cl := (Step.hole 2 4 3).line
include leaf in
private theorem tree314 : P c314 1 := leaf _ (.inr ⟨2,4,3,by decide,rfl⟩)

private def c315 : Cl := {((2,0),true),((2,1),true),((2,2),true),((4,3),false)}
include leaf fork in
private theorem tree315 : P c315 2 := fork (tree313 P leaf) (tree314 P leaf) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c316 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree316 : P c316 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c317 : Cl := (Step.hole 3 4 3).line
include leaf in
private theorem tree317 : P c317 1 := leaf _ (.inr ⟨3,4,3,by decide,rfl⟩)

private def c318 : Cl := {((3,0),true),((3,1),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree318 : P c318 2 := fork (tree316 P leaf) (tree317 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c319 : Cl := (Step.hole 2 3 1).line
include leaf in
private theorem tree319 : P c319 1 := leaf _ (.inr ⟨2,3,1,by decide,rfl⟩)

private def c320 : Cl := {((2,1),false),((3,0),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree320 : P c320 3 := fork (tree318 P leaf fork) (tree319 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c321 : Cl := {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,3),false)}
include leaf fork in
private theorem tree321 : P c321 5 := fork (tree315 P leaf fork) (tree320 P leaf fork) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c322 : Cl := {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree322 : P c322 6 := fork (tree312 P leaf) (tree321 P leaf fork) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c323 : Cl := (Step.hole 1 4 2).line
include leaf in
private theorem tree323 : P c323 1 := leaf _ (.inr ⟨1,4,2,by decide,rfl⟩)

private def c324 : Cl := {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree324 : P c324 7 := fork (tree322 P leaf fork) (tree323 P leaf) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c325 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree325 : P c325 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c326 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree326 : P c326 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c327 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree327 : P c327 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c328 : Cl := {((2,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree328 : P c328 2 := fork (tree326 P leaf) (tree327 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c329 : Cl := (Step.hole 3 4 1).line
include leaf in
private theorem tree329 : P c329 1 := leaf _ (.inr ⟨3,4,1,by decide,rfl⟩)

private def c330 : Cl := {((2,3),false),((3,0),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree330 : P c330 3 := fork (tree328 P leaf fork) (tree329 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c331 : Cl := {((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree331 : P c331 4 := fork (tree325 P leaf) (tree330 P leaf fork) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c332 : Cl := (Step.hole 2 4 1).line
include leaf in
private theorem tree332 : P c332 1 := leaf _ (.inr ⟨2,4,1,by decide,rfl⟩)

private def c333 : Cl := {((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,1),false)}
include leaf fork in
private theorem tree333 : P c333 5 := fork (tree331 P leaf fork) (tree332 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c334 : Cl := {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((3,2),true),((4,0),true)}
include leaf fork in
private theorem tree334 : P c334 12 := fork (tree324 P leaf fork) (tree333 P leaf fork) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c335 : Cl := (Step.hole 1 3 2).line
include leaf in
private theorem tree335 : P c335 1 := leaf _ (.inr ⟨1,3,2,by decide,rfl⟩)

private def c336 : Cl := {((1,2),false),((2,0),true),((2,2),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree336 : P c336 13 := fork (tree334 P leaf fork) (tree335 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c337 : Cl := (Step.hole 1 2 2).line
include leaf in
private theorem tree337 : P c337 1 := leaf _ (.inr ⟨1,2,2,by decide,rfl⟩)

private def c338 : Cl := {((1,2),false),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree338 : P c338 14 := fork (tree336 P leaf fork) (tree337 P leaf) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c339 : Cl := {((1,0),true),((1,1),true),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree339 : P c339 29 := fork (tree311 P leaf fork) (tree338 P leaf fork) ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c340 : Cl := (Step.pigeon 2).line
include leaf in
private theorem tree340 : P c340 1 := leaf _ (.inl ⟨2,rfl⟩)

private def c341 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree341 : P c341 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c342 : Cl := (Step.hole 2 3 3).line
include leaf in
private theorem tree342 : P c342 1 := leaf _ (.inr ⟨2,3,3,by decide,rfl⟩)

private def c343 : Cl := {((2,3),false),((3,0),true),((3,1),true),((3,2),true)}
include leaf fork in
private theorem tree343 : P c343 2 := fork (tree341 P leaf) (tree342 P leaf) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c344 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree344 : P c344 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c345 : Cl := (Step.hole 2 4 3).line
include leaf in
private theorem tree345 : P c345 1 := leaf _ (.inr ⟨2,4,3,by decide,rfl⟩)

private def c346 : Cl := {((2,3),false),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree346 : P c346 2 := fork (tree344 P leaf) (tree345 P leaf) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c347 : Cl := (Step.hole 3 4 2).line
include leaf in
private theorem tree347 : P c347 1 := leaf _ (.inr ⟨3,4,2,by decide,rfl⟩)

private def c348 : Cl := {((2,3),false),((3,2),false),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree348 : P c348 3 := fork (tree346 P leaf fork) (tree347 P leaf) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c349 : Cl := {((2,3),false),((3,0),true),((3,1),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree349 : P c349 5 := fork (tree343 P leaf fork) (tree348 P leaf fork) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c350 : Cl := {((2,0),true),((2,1),true),((2,2),true),((3,0),true),((3,1),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree350 : P c350 6 := fork (tree340 P leaf) (tree349 P leaf fork) ⟨(2,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c351 : Cl := (Step.pigeon 3).line
include leaf in
private theorem tree351 : P c351 1 := leaf _ (.inl ⟨3,rfl⟩)

private def c352 : Cl := (Step.pigeon 4).line
include leaf in
private theorem tree352 : P c352 1 := leaf _ (.inl ⟨4,rfl⟩)

private def c353 : Cl := (Step.hole 3 4 3).line
include leaf in
private theorem tree353 : P c353 1 := leaf _ (.inr ⟨3,4,3,by decide,rfl⟩)

private def c354 : Cl := {((3,3),false),((4,0),true),((4,1),true),((4,2),true)}
include leaf fork in
private theorem tree354 : P c354 2 := fork (tree352 P leaf) (tree353 P leaf) ⟨(4,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c355 : Cl := (Step.hole 2 4 2).line
include leaf in
private theorem tree355 : P c355 1 := leaf _ (.inr ⟨2,4,2,by decide,rfl⟩)

private def c356 : Cl := {((2,2),false),((3,3),false),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree356 : P c356 3 := fork (tree354 P leaf fork) (tree355 P leaf) ⟨(4,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c357 : Cl := {((2,2),false),((3,0),true),((3,1),true),((3,2),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree357 : P c357 4 := fork (tree351 P leaf) (tree356 P leaf fork) ⟨(3,3),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c358 : Cl := (Step.hole 2 3 2).line
include leaf in
private theorem tree358 : P c358 1 := leaf _ (.inr ⟨2,3,2,by decide,rfl⟩)

private def c359 : Cl := {((2,2),false),((3,0),true),((3,1),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree359 : P c359 5 := fork (tree357 P leaf fork) (tree358 P leaf) ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c360 : Cl := {((2,0),true),((2,1),true),((3,0),true),((3,1),true),((4,0),true),((4,1),true)}
include leaf fork in
private theorem tree360 : P c360 11 := fork (tree350 P leaf fork) (tree359 P leaf fork) ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c361 : Cl := (Step.hole 1 4 1).line
include leaf in
private theorem tree361 : P c361 1 := leaf _ (.inr ⟨1,4,1,by decide,rfl⟩)

private def c362 : Cl := {((1,1),false),((2,0),true),((2,1),true),((3,0),true),((3,1),true),((4,0),true)}
include leaf fork in
private theorem tree362 : P c362 12 := fork (tree360 P leaf fork) (tree361 P leaf) ⟨(4,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c363 : Cl := (Step.hole 1 3 1).line
include leaf in
private theorem tree363 : P c363 1 := leaf _ (.inr ⟨1,3,1,by decide,rfl⟩)

private def c364 : Cl := {((1,1),false),((2,0),true),((2,1),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree364 : P c364 13 := fork (tree362 P leaf fork) (tree363 P leaf) ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c365 : Cl := (Step.hole 1 2 1).line
include leaf in
private theorem tree365 : P c365 1 := leaf _ (.inr ⟨1,2,1,by decide,rfl⟩)

private def c366 : Cl := {((1,1),false),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree366 : P c366 14 := fork (tree364 P leaf fork) (tree365 P leaf) ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c367 : Cl := {((1,0),true),((2,0),true),((3,0),true),((4,0),true)}
include leaf fork in
private theorem tree367 : P c367 43 := fork (tree339 P leaf fork) (tree366 P leaf fork) ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c368 : Cl := (Step.hole 0 4 0).line
include leaf in
private theorem tree368 : P c368 1 := leaf _ (.inr ⟨0,4,0,by decide,rfl⟩)

private def c369 : Cl := {((0,0),false),((1,0),true),((2,0),true),((3,0),true)}
include leaf fork in
private theorem tree369 : P c369 44 := fork (tree367 P leaf fork) (tree368 P leaf) ⟨(4,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c370 : Cl := (Step.hole 0 3 0).line
include leaf in
private theorem tree370 : P c370 1 := leaf _ (.inr ⟨0,3,0,by decide,rfl⟩)

private def c371 : Cl := {((0,0),false),((1,0),true),((2,0),true)}
include leaf fork in
private theorem tree371 : P c371 45 := fork (tree369 P leaf fork) (tree370 P leaf) ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c372 : Cl := (Step.hole 0 2 0).line
include leaf in
private theorem tree372 : P c372 1 := leaf _ (.inr ⟨0,2,0,by decide,rfl⟩)

private def c373 : Cl := {((0,0),false),((1,0),true)}
include leaf fork in
private theorem tree373 : P c373 46 := fork (tree371 P leaf fork) (tree372 P leaf) ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c374 : Cl := (Step.hole 0 1 0).line
include leaf in
private theorem tree374 : P c374 1 := leaf _ (.inr ⟨0,1,0,by decide,rfl⟩)

private def c375 : Cl := {((0,0),false)}
include leaf fork in
private theorem tree375 : P c375 47 := fork (tree373 P leaf fork) (tree374 P leaf) ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

private def c376 : Cl := ∅
include leaf fork in
private theorem tree376 : P c376 189 := fork (tree282 P leaf fork) (tree375 P leaf fork) ⟨(0,0),by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Recursion principle witness for an ordinary resolution tree with exactly 189 axiom leaves. -/
theorem _root_.Row169.tree377 (P : Clause (Fin 5 × Fin 4) → ℕ → Prop)
    (leaf : ∀ C ∈ PHP 5 4, P C 1)
    (fork : ∀ {A B R} {l r : ℕ}, P A l → P B r → IsResolvent A B R → P R (l+r)) :
    P ∅ 189 := tree376 P leaf fork
end Tree

end Row169.Budget377
