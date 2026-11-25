import PEqualNP.Defs

namespace Row133.QueryTree
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

/-- Leaf occurrences count copies separately if a derivation DAG is unrolled. -/
inductive ResolutionTree (F : Set (Clause V)) : Clause V → Nat → Prop
  | ax {C} (h : C ∈ F) : ResolutionTree F C 1
  | resolve {C D R i j} (left : ResolutionTree F C i) (right : ResolutionTree F D j)
      (rule : IsResolvent C D R) : ResolutionTree F R (i+j)
  | weaken {C D i} (parent : ResolutionTree F C i)
      (rule : ∀ a : V → Bool, ClauseSat a C → ClauseSat a D) : ResolutionTree F D i

abbrev Partial (V : Type) := V → Option Bool

def Agrees (p : Partial V) (a : V → Bool) : Prop := ∀ v b, p v = some b → a v = b

def ForcesFalse (p : Partial V) (C : Clause V) := ∀ a, Agrees p a → ¬ ClauseSat a C

/-- Only previously unknown coordinates can be queried. -/
inductive SearchTree (F : Set (Clause V)) : Partial V → Nat → Prop
  | leaf {p C} (h : C ∈ F) (falsified : ForcesFalse p C) : SearchTree F p 1
  | ask {p i j} (v : V) (fresh : p v = none)
      (left : SearchTree F (Function.update p v (some false)) i)
      (right : SearchTree F (Function.update p v (some true)) j) : SearchTree F p (i+j)

private theorem extendsUpdate {p : Partial V} {a : V → Bool} {v b}
    (fresh : p v = none) (h : Agrees (Function.update p v (some b)) a) : Agrees p a := by
  intro u t hu
  by_cases eq : u = v
  · subst u; simp_all
  · exact h u t (by simpa [Function.update_of_ne eq] using hu)

private theorem atUpdate {p : Partial V} {a : V → Bool} {v b}
    (h : Agrees (Function.update p v (some b)) a) : a v = b :=
  h v b (Function.update_self ..)

private theorem parentFalse {a : V → Bool} {C R : Clause V} {v s}
    (sub : C.erase (v,s) ⊆ R) (absent : ¬ ClauseSat a R) (opposite : a v ≠ s) : ¬ ClauseSat a C := by
  rintro ⟨l,hl,hs⟩
  by_cases eq : l = (v,s)
  · subst l; exact opposite hs
  · exact absent ⟨l,sub (Finset.mem_erase.mpr ⟨eq,hl⟩),hs⟩

/-- Follow the parent whose pivot literal is false. Repeated queries disappear and a
semantic weakening changes no branch. The resulting search has no more leaf occurrences. -/
theorem traverse {F : Set (Clause V)} {C : Clause V} {L : Nat} (t : ResolutionTree F C L)
    (p : Partial V) (h : ForcesFalse p C) : ∃ k ≤ L, SearchTree F p k := by
  induction t generalizing p with
  | ax axiomIn => exact ⟨1, le_rfl, .leaf axiomIn h⟩
  | weaken parent rule ih => exact ih p (fun a ha hc => h a ha (rule a hc))
  | @resolve C D R i j left right rule ihl ihr =>
    obtain ⟨v,_,_,rfl⟩ := rule
    have lsub : C.erase (v,true) ⊆ C.erase (v,true) ∪ D.erase (v,false) := Finset.subset_union_left
    have rsub : D.erase (v,false) ⊆ C.erase (v,true) ∪ D.erase (v,false) := Finset.subset_union_right
    cases known : p v with
    | none =>
      obtain ⟨kl,hkl,tl⟩ := ihl (Function.update p v (some false)) (fun a ha =>
        parentFalse lsub (h a (extendsUpdate known ha)) (by simp [atUpdate ha]))
      obtain ⟨kr,hkr,tr⟩ := ihr (Function.update p v (some true)) (fun a ha =>
        parentFalse rsub (h a (extendsUpdate known ha)) (by simp [atUpdate ha]))
      exact ⟨kl+kr,by omega,.ask v known tl tr⟩
    | some b =>
      cases b with
      | false =>
        obtain ⟨k,hk,t⟩ := ihl p (fun a ha => parentFalse lsub (h a ha) (by simp [ha v false known]))
        exact ⟨k,by omega,t⟩
      | true =>
        obtain ⟨k,hk,t⟩ := ihr p (fun a ha => parentFalse rsub (h a ha) (by simp [ha v true known]))
        exact ⟨k,by omega,t⟩

theorem fromRefutation {F : Set (Clause V)} {L : Nat} (t : ResolutionTree F ∅ L) :
    ∃ k ≤ L, SearchTree F (fun _ => none) k :=
  traverse t _ (by simp [ForcesFalse,ClauseSat])

private theorem forcedLiteral {p : Partial V} {C : Clause V} (hf : ForcesFalse p C)
    {v : V} {b : Bool} (mem : (v,b) ∈ C) : p v = some (!b) := by
  classical
  let a : V → Bool := fun u => (p u).getD (if u = v then b else false)
  have agrees : Agrees p a := by intro u b hu; simp [a,hu]
  have ne : a v ≠ b := fun e => hf a agrees ⟨(v,b),mem,e⟩
  cases hv : p v with
  | none => simp [a,hv] at ne
  | some x => cases b <;> cases x <;> simp_all [a]

/-- A terminal bit-pigeonhole leaf fixes the two full bit strings to one common hole. -/
theorem collision {m l : Nat} {p : Partial (Fin m × Fin l)} {C : Clause (Fin m × Fin l)}
    (ax : C ∈ BPHP m l) (hf : ForcesFalse p C) :
    ∃ i j : Fin m, ∃ hole : Fin l → Bool, i ≠ j ∧
      ∀ b, p (i,b) = some (hole b) ∧ p (j,b) = some (hole b) := by
  obtain ⟨i,j,hole,ne,rfl⟩ := ax
  refine ⟨i,j,hole,ne,fun b => ⟨?_,?_⟩⟩
  · simpa using forcedLiteral hf (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩) : ((i,b),!hole b) ∈ _)
  · simpa using forcedLiteral hf (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩) : ((j,b),!hole b) ∈ _)
end Row133.QueryTree
#print axioms Row133.QueryTree.fromRefutation
#print axioms Row133.QueryTree.collision
