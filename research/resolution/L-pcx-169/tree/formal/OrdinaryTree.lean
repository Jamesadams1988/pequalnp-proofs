import QueryTree

namespace Row169.OrdinaryTree
open PEqualNP.ProofComplexity Row133.QueryTree
variable {V : Type} [DecidableEq V]

/-- Ordinary trees use only input axioms and the project's syntactic resolution rule. -/
inductive PureTree (F : Set (Clause V)) : Clause V → Nat → Prop
  | ax {C} (member : C ∈ F) : PureTree F C 1
  | res {C D R l r} (left : PureTree F C l) (right : PureTree F D r)
      (rule : IsResolvent C D R) : PureTree F R (l+r)

private def Fixed (p : Partial V) (C : Clause V) :=
  ∀ v b, (v,b) ∈ C → p v = some (!b)

private theorem fixedOfFalse {p : Partial V} {C : Clause V} (h : ForcesFalse p C) : Fixed p C := by
  intro v b mem
  let a : V → Bool := fun u => (p u).getD (if u = v then b else false)
  have agrees : Agrees p a := by intro u b hu; simp [a,hu]
  have ne : a v ≠ b := fun e => h a agrees ⟨(v,b),mem,e⟩
  cases hv : p v with
  | none => simp [a,hv] at ne
  | some x => cases b <;> cases x <;> simp_all [a]

private theorem forgetPivot {p : Partial V} {v : V} {b : Bool} {C : Clause V}
    (h : Fixed (Function.update p v (some b)) C) {u : V} {s : Bool}
    (hs : (u,s) ∈ C) (hne : (u,s) ≠ (v,!b)) : p u = some (!s) := by
  have val := h u s hs
  by_cases eq : u = v
  · subst u
    simp only [Function.update_self,Option.some.injEq] at val
    have e : s = !b := by cases b <;> cases s <;> first | rfl | cases val
    exact (hne (Prod.ext rfl e)).elim
  · simpa [Function.update_of_ne eq] using val

private theorem extract {F : Set (Clause V)} {p : Partial V} {k : Nat} (t : SearchTree F p k) :
    ∃ C m, m ≤ k ∧ PureTree F C m ∧ Fixed p C := by
  induction t with
  | leaf hm hf => exact ⟨_,1,le_rfl,.ax hm,fixedOfFalse hf⟩
  | @ask p i j v fresh tl tr ihl ihr =>
    obtain ⟨C,m,hm,tC,fC⟩ := ihl
    obtain ⟨D,n,hn,tD,fD⟩ := ihr
    by_cases pos : (v,true) ∈ C
    · by_cases neg : (v,false) ∈ D
      · refine ⟨C.erase (v,true) ∪ D.erase (v,false),m+n,by omega,.res tC tD ⟨v,pos,neg,rfl⟩,?_⟩
        intro u s hs
        rcases Finset.mem_union.mp hs with l|r
        · obtain ⟨neq,mem⟩ := Finset.mem_erase.mp l
          exact forgetPivot fC mem neq
        · obtain ⟨neq,mem⟩ := Finset.mem_erase.mp r
          exact forgetPivot fD mem neq
      · exact ⟨D,n,by omega,tD,fun u s hs => forgetPivot fD hs (fun eq => neg (eq ▸ hs))⟩
    · exact ⟨C,m,by omega,tC,fun u s hs => forgetPivot fC hs (fun eq => pos (eq ▸ hs))⟩

/-- A Boolean query tree that solves the axiom-search problem yields a pure ordinary resolution
refutation with at most its leaf count. Missing pivot literals let us retain one subtree. -/
theorem queryToResolution {F : Set (Clause V)} {k : Nat} (t : SearchTree F (fun _ => none) k) :
    ∃ m ≤ k, PureTree F ∅ m := by
  obtain ⟨C,m,h,tC,fC⟩ := extract t
  have empty : C = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨v,b⟩ mem
    simpa using fC v b mem
  exact ⟨m,h,empty ▸ tC⟩

private theorem forget {F : Set (Clause V)} {C : Clause V} {l} (t : PureTree F C l) :
    ResolutionTree F C l := by
  induction t with
  | ax h => exact .ax h
  | res tl tr rule il ir => exact .resolve il ir rule

/-- The minima agree, although either individual translation can prune the source tree. -/
theorem sameLeafBudgets (F : Set (Clause V)) (k : Nat) :
    (∃ m ≤ k, PureTree F ∅ m) ↔ ∃ m ≤ k, SearchTree F (fun _ => none) m := by
  constructor
  · rintro ⟨m,hm,t⟩
    obtain ⟨i,hi,u⟩ := fromRefutation (forget t)
    exact ⟨i,by omega,u⟩
  · rintro ⟨m,hm,t⟩
    obtain ⟨i,hi,u⟩ := queryToResolution t
    exact ⟨i,by omega,u⟩

private theorem appendDeriv {F : Set (Clause V)} {a b : List (Clause V)}
    (ha : IsDerivation F a) (hb : IsDerivation F b) : IsDerivation F (a ++ b) := by
  induction ha with
  | nil => exact hb
  | ax prev hc ih => exact .ax ih hc
  | res prev cp dp rule ih => exact .res ih (List.mem_append_left _ cp) (List.mem_append_left _ dp) rule

/-- Serialization counts a separate copy of each tree occurrence. -/
theorem serialize {F : Set (Clause V)} {C : Clause V} {l : Nat} (t : PureTree F C l) :
    ∃ π, IsDerivation F π ∧ C ∈ π ∧ π.length + 1 = 2*l := by
  induction t with
  | ax h => exact ⟨[_],.ax .nil h,by simp,rfl⟩
  | @res C D R l r tl tr rule il ir =>
    obtain ⟨a,da,ca,la⟩ := il
    obtain ⟨b,db,cb,lb⟩ := ir
    exact ⟨R :: (a++b),.res (appendDeriv da db) (List.mem_append_left _ ca)
      (List.mem_append_right _ cb) rule,by simp,by simp only [List.length_cons,List.length_append]; omega⟩
omit [DecidableEq V] in
private theorem falseOfFixed {p : Partial V} {C : Clause V} (h : Fixed p C) : ForcesFalse p C := by
  intro a ha; rintro ⟨⟨v,b⟩,mem,sat⟩
  have eq := ha v (!b) (h v b mem)
  have ne : b ≠ !b := by cases b <;> decide
  exact ne (sat.symm.trans eq)

/-- Exact terminal test for the full Boolean-matrix search. Pigeons are allowed to occupy
multiple holes in partial or total assignments. -/
theorem unaryTerminal {m n : Nat} (p : Partial (Fin m × Fin n)) :
    (∃ C ∈ PHP m n, ForcesFalse p C) ↔
    (∃ i, ∀ j, p (i,j) = some false) ∨
      ∃ i k j, i ≠ k ∧ p (i,j) = some true ∧ p (k,j) = some true := by
  constructor
  · rintro ⟨C,(⟨i,rfl⟩ | ⟨i,k,j,ne,rfl⟩),h⟩
    · exact .inl ⟨i,fun j => fixedOfFalse h (i,j) true (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
    · exact .inr ⟨i,k,j,ne,fixedOfFalse h (i,j) false (by simp),fixedOfFalse h (k,j) false (by simp)⟩
  · rintro (⟨i,row⟩ | ⟨i,k,j,ne,ci,ck⟩)
    · refine ⟨_,.inl ⟨i,rfl⟩,falseOfFixed ?_⟩
      intro v b hv
      obtain ⟨h,_,eq⟩ := Finset.mem_image.mp hv
      cases eq; exact row h
    · refine ⟨_,.inr ⟨i,k,j,ne,rfl⟩,falseOfFixed ?_⟩
      intro v b hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with eq|eq <;> cases eq
      · exact ci
      · exact ck

end Row169.OrdinaryTree
#print axioms Row169.OrdinaryTree.sameLeafBudgets
#print axioms Row169.OrdinaryTree.serialize
#print axioms Row169.OrdinaryTree.unaryTerminal
