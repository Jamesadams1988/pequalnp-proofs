import PEqualNP.Defs

namespace Row169.Budget157
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
  .pigeon 1,
  .pigeon 2,
  .pigeon 3,
  .pigeon 4,
  .hole 0 1 0,
  .hole 0 1 1,
  .hole 0 1 2,
  .hole 0 1 3,
  .hole 0 2 0,
  .hole 0 2 1,
  .hole 0 2 2,
  .hole 0 2 3,
  .hole 1 2 0,
  .hole 1 2 1,
  .hole 1 2 2,
  .hole 1 2 3,
  .hole 0 3 0,
  .hole 0 3 1,
  .hole 0 3 2,
  .hole 0 3 3,
  .hole 1 3 0,
  .hole 1 3 1,
  .hole 1 3 2,
  .hole 1 3 3,
  .hole 2 3 0,
  .hole 2 3 1,
  .hole 2 3 2,
  .hole 2 3 3,
  .hole 0 4 0,
  .hole 0 4 1,
  .hole 0 4 2,
  .hole 0 4 3,
  .hole 1 4 0,
  .hole 1 4 1,
  .hole 1 4 2,
  .hole 1 4 3,
  .hole 2 4 0,
  .hole 2 4 1,
  .hole 2 4 2,
  .hole 2 4 3,
  .hole 3 4 0,
  .hole 3 4 1,
  .hole 3 4 2,
  .hole 3 4 3,
  .resolve 44 39 (0,0) {((0,1),true),((0,2),true),((0,3),true),((1,0),false)},
  .resolve 44 0 (1,0) {((0,1),true),((0,2),true),((0,3),true),((1,1),true),((1,2),true),((1,3),true)},
  .resolve 46 40 (0,1) {((0,0),true),((0,2),true),((0,3),true),((1,1),false)},
  .resolve 46 0 (1,1) {((0,0),true),((0,2),true),((0,3),true),((1,0),true),((1,2),true),((1,3),true)},
  .resolve 48 41 (0,2) {((0,0),true),((0,1),true),((0,3),true),((1,2),false)},
  .resolve 48 0 (1,2) {((0,0),true),((0,1),true),((0,3),true),((1,0),true),((1,1),true),((1,3),true)},
  .resolve 50 42 (0,3) {((0,0),true),((0,1),true),((0,2),true),((1,3),false)},
  .resolve 50 0 (1,3) {((0,0),true),((0,1),true),((0,2),true),((1,0),true),((1,1),true),((1,2),true)},
  .resolve 4 43 (0,0) {((0,2),true),((0,3),true),((1,0),true),((1,2),true),((1,3),true),((2,0),false)},
  .resolve 0 40 (1,0) {((0,2),true),((0,3),true),((1,2),true),((1,3),true),((2,0),false)},
  .resolve 52 0 (2,0) {((0,2),true),((0,3),true),((1,2),true),((1,3),true),((2,1),true),((2,2),true),((2,3),true)},
  .resolve 9 45 (0,1) {((0,2),true),((0,3),true),((1,1),true),((1,2),true),((1,3),true),((2,1),false)},
  .resolve 0 42 (1,1) {((0,2),true),((0,3),true),((1,2),true),((1,3),true),((2,1),false)},
  .resolve 2 0 (2,1) {((0,2),true),((0,3),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true)},
  .resolve 8 49 (0,0) {((0,1),true),((0,3),true),((1,0),true),((1,1),true),((1,3),true),((2,0),false)},
  .resolve 0 46 (1,0) {((0,1),true),((0,3),true),((1,1),true),((1,3),true),((2,0),false)},
  .resolve 58 0 (2,0) {((0,1),true),((0,3),true),((1,1),true),((1,3),true),((2,1),true),((2,2),true),((2,3),true)},
  .resolve 15 50 (0,2) {((0,1),true),((0,3),true),((1,1),true),((1,2),true),((1,3),true),((2,2),false)},
  .resolve 0 47 (1,2) {((0,1),true),((0,3),true),((1,1),true),((1,3),true),((2,2),false)},
  .resolve 2 0 (2,2) {((0,1),true),((0,3),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true)},
  .resolve 12 55 (0,0) {((0,1),true),((0,2),true),((1,0),true),((1,1),true),((1,2),true),((2,0),false)},
  .resolve 0 52 (1,0) {((0,1),true),((0,2),true),((1,1),true),((1,2),true),((2,0),false)},
  .resolve 64 0 (2,0) {((0,1),true),((0,2),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((2,3),true)},
  .resolve 21 55 (0,3) {((0,1),true),((0,2),true),((1,1),true),((1,2),true),((1,3),true),((2,3),false)},
  .resolve 0 52 (1,3) {((0,1),true),((0,2),true),((1,1),true),((1,2),true),((2,3),false)},
  .resolve 2 0 (2,3) {((0,1),true),((0,2),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true)},
  .resolve 20 60 (0,1) {((0,0),true),((0,3),true),((1,0),true),((1,1),true),((1,3),true),((2,1),false)},
  .resolve 0 57 (1,1) {((0,0),true),((0,3),true),((1,0),true),((1,3),true),((2,1),false)},
  .resolve 70 0 (2,1) {((0,0),true),((0,3),true),((1,0),true),((1,3),true),((2,0),true),((2,2),true),((2,3),true)},
  .resolve 25 62 (0,2) {((0,0),true),((0,3),true),((1,0),true),((1,2),true),((1,3),true),((2,2),false)},
  .resolve 0 59 (1,2) {((0,0),true),((0,3),true),((1,0),true),((1,3),true),((2,2),false)},
  .resolve 2 0 (2,2) {((0,0),true),((0,3),true),((1,0),true),((1,3),true),((2,0),true),((2,3),true)},
  .resolve 24 66 (0,1) {((0,0),true),((0,2),true),((1,0),true),((1,1),true),((1,2),true),((2,1),false)},
  .resolve 0 63 (1,1) {((0,0),true),((0,2),true),((1,0),true),((1,2),true),((2,1),false)},
  .resolve 76 0 (2,1) {((0,0),true),((0,2),true),((1,0),true),((1,2),true),((2,0),true),((2,2),true),((2,3),true)},
  .resolve 31 67 (0,3) {((0,0),true),((0,2),true),((1,0),true),((1,2),true),((1,3),true),((2,3),false)},
  .resolve 0 64 (1,3) {((0,0),true),((0,2),true),((1,0),true),((1,2),true),((2,3),false)},
  .resolve 2 0 (2,3) {((0,0),true),((0,2),true),((1,0),true),((1,2),true),((2,0),true),((2,2),true)},
  .resolve 30 71 (0,2) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((1,2),true),((2,2),false)},
  .resolve 0 68 (1,2) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((2,2),false)},
  .resolve 82 0 (2,2) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((2,0),true),((2,1),true),((2,3),true)},
  .resolve 35 73 (0,3) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((1,3),true),((2,3),false)},
  .resolve 0 70 (1,3) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((2,3),false)},
  .resolve 2 0 (2,3) {((0,0),true),((0,1),true),((1,0),true),((1,1),true),((2,0),true),((2,1),true)},
  .resolve 12 71 (0,0) {((0,3),true),((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,0),false)},
  .resolve 0 68 (1,0) {((0,3),true),((1,3),true),((2,0),true),((2,3),true),((3,0),false)},
  .resolve 0 65 (2,0) {((0,3),true),((1,3),true),((2,3),true),((3,0),false)},
  .resolve 88 0 (3,0) {((0,3),true),((1,3),true),((2,3),true),((3,1),true),((3,2),true),((3,3),true)},
  .resolve 28 74 (0,1) {((0,3),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,1),false)},
  .resolve 0 71 (1,1) {((0,3),true),((1,3),true),((2,1),true),((2,3),true),((3,1),false)},
  .resolve 0 68 (2,1) {((0,3),true),((1,3),true),((2,3),true),((3,1),false)},
  .resolve 3 0 (3,1) {((0,3),true),((1,3),true),((2,3),true),((3,2),true),((3,3),true)},
  .resolve 38 77 (0,2) {((0,3),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,2),false)},
  .resolve 0 74 (1,2) {((0,3),true),((1,3),true),((2,2),true),((2,3),true),((3,2),false)},
  .resolve 0 71 (2,2) {((0,3),true),((1,3),true),((2,3),true),((3,2),false)},
  .resolve 3 0 (3,2) {((0,3),true),((1,3),true),((2,3),true),((3,3),true)},
  .resolve 18 83 (0,0) {((0,2),true),((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,0),false)},
  .resolve 0 80 (1,0) {((0,2),true),((1,2),true),((2,0),true),((2,2),true),((3,0),false)},
  .resolve 0 77 (2,0) {((0,2),true),((1,2),true),((2,2),true),((3,0),false)},
  .resolve 100 0 (3,0) {((0,2),true),((1,2),true),((2,2),true),((3,1),true),((3,2),true),((3,3),true)},
  .resolve 34 86 (0,1) {((0,2),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,1),false)},
  .resolve 0 83 (1,1) {((0,2),true),((1,2),true),((2,1),true),((2,2),true),((3,1),false)},
  .resolve 0 80 (2,1) {((0,2),true),((1,2),true),((2,2),true),((3,1),false)},
  .resolve 3 0 (3,1) {((0,2),true),((1,2),true),((2,2),true),((3,2),true),((3,3),true)},
  .resolve 50 88 (0,3) {((0,2),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true),((3,3),false)},
  .resolve 0 85 (1,3) {((0,2),true),((1,2),true),((2,2),true),((2,3),true),((3,3),false)},
  .resolve 0 82 (2,3) {((0,2),true),((1,2),true),((2,2),true),((3,3),false)},
  .resolve 3 0 (3,3) {((0,2),true),((1,2),true),((2,2),true),((3,2),true)},
  .resolve 24 95 (0,0) {((0,1),true),((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,0),false)},
  .resolve 0 92 (1,0) {((0,1),true),((1,1),true),((2,0),true),((2,1),true),((3,0),false)},
  .resolve 0 89 (2,0) {((0,1),true),((1,1),true),((2,1),true),((3,0),false)},
  .resolve 112 0 (3,0) {((0,1),true),((1,1),true),((2,1),true),((3,1),true),((3,2),true),((3,3),true)},
  .resolve 46 97 (0,2) {((0,1),true),((1,1),true),((1,2),true),((2,1),true),((2,2),true),((3,2),false)},
  .resolve 0 94 (1,2) {((0,1),true),((1,1),true),((2,1),true),((2,2),true),((3,2),false)},
  .resolve 0 91 (2,2) {((0,1),true),((1,1),true),((2,1),true),((3,2),false)},
  .resolve 3 0 (3,2) {((0,1),true),((1,1),true),((2,1),true),((3,1),true),((3,3),true)},
  .resolve 56 100 (0,3) {((0,1),true),((1,1),true),((1,3),true),((2,1),true),((2,3),true),((3,3),false)},
  .resolve 0 97 (1,3) {((0,1),true),((1,1),true),((2,1),true),((2,3),true),((3,3),false)},
  .resolve 0 94 (2,3) {((0,1),true),((1,1),true),((2,1),true),((3,3),false)},
  .resolve 3 0 (3,3) {((0,1),true),((1,1),true),((2,1),true),((3,1),true)},
  .resolve 36 106 (0,1) {((0,0),true),((1,0),true),((1,1),true),((2,0),true),((2,1),true),((3,1),false)},
  .resolve 0 103 (1,1) {((0,0),true),((1,0),true),((2,0),true),((2,1),true),((3,1),false)},
  .resolve 0 100 (2,1) {((0,0),true),((1,0),true),((2,0),true),((3,1),false)},
  .resolve 124 0 (3,1) {((0,0),true),((1,0),true),((2,0),true),((3,0),true),((3,2),true),((3,3),true)},
  .resolve 46 109 (0,2) {((0,0),true),((1,0),true),((1,2),true),((2,0),true),((2,2),true),((3,2),false)},
  .resolve 0 106 (1,2) {((0,0),true),((1,0),true),((2,0),true),((2,2),true),((3,2),false)},
  .resolve 0 103 (2,2) {((0,0),true),((1,0),true),((2,0),true),((3,2),false)},
  .resolve 3 0 (3,2) {((0,0),true),((1,0),true),((2,0),true),((3,0),true),((3,3),true)},
  .resolve 56 112 (0,3) {((0,0),true),((1,0),true),((1,3),true),((2,0),true),((2,3),true),((3,3),false)},
  .resolve 0 109 (1,3) {((0,0),true),((1,0),true),((2,0),true),((2,3),true),((3,3),false)},
  .resolve 0 106 (2,3) {((0,0),true),((1,0),true),((2,0),true),((3,3),false)},
  .resolve 3 0 (3,3) {((0,0),true),((1,0),true),((2,0),true),((3,0),true)},
  .resolve 0 107 (0,0) {((1,0),true),((2,0),true),((3,0),true),((4,0),false)},
  .resolve 0 104 (1,0) {((2,0),true),((3,0),true),((4,0),false)},
  .resolve 0 101 (2,0) {((3,0),true),((4,0),false)},
  .resolve 0 98 (3,0) {((4,0),false)},
  .resolve 136 0 (4,0) {((4,1),true),((4,2),true),((4,3),true)},
  .resolve 17 111 (0,1) {((1,1),true),((2,1),true),((3,1),true),((4,1),false)},
  .resolve 0 108 (1,1) {((2,1),true),((3,1),true),((4,1),false)},
  .resolve 0 105 (2,1) {((3,1),true),((4,1),false)},
  .resolve 0 102 (3,1) {((4,1),false)},
  .resolve 4 0 (4,1) {((4,2),true),((4,3),true)},
  .resolve 34 115 (0,2) {((1,2),true),((2,2),true),((3,2),true),((4,2),false)},
  .resolve 0 112 (1,2) {((2,2),true),((3,2),true),((4,2),false)},
  .resolve 0 109 (2,2) {((3,2),true),((4,2),false)},
  .resolve 0 106 (3,2) {((4,2),false)},
  .resolve 4 0 (4,2) {((4,3),true)},
  .resolve 51 119 (0,3) {((1,3),true),((2,3),true),((3,3),true),((4,3),false)},
  .resolve 0 116 (1,3) {((2,3),true),((3,3),true),((4,3),false)},
  .resolve 0 113 (2,3) {((3,3),true),((4,3),false)},
  .resolve 0 110 (3,3) {((4,3),false)},
  .resolve 4 0 (4,3) ∅]

private theorem checks : verify steps [] = true := by decide +kernel

private def proofLines : List Cl := (steps.map Step.line).reverse

private theorem derives : IsDerivation (PHP 5 4) proofLines := by
  simpa [proofLines] using verifySound steps [] .nil checks

theorem _root_.Row169.refutation157 :
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)),
      PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 157 :=
  ⟨proofLines,⟨derives,by decide +kernel⟩,by decide +kernel⟩

end Row169.Budget157
