import PEqualNP.Defs

namespace CliqueEdges
open PEqualNP.ProofComplexity PEqualNP.Search
abbrev Var := Fin 4
abbrev L := CPLine Var

/-- The six edges index the six negative two-literal clauses. -/
def ends : Fin 6 → Var × Var := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def pairClause (k : Fin 6) : Clause Var := {((ends k).1,false),((ends k).2,false)}
def edges : Set (Clause Var) := Set.range pairClause
def point (k : Fin 6) (i : Var) : Bool := decide (i = (ends k).1 ∨ i = (ends k).2)
def cap : L := (fun _ => -1,-1)
def lo (i : Var) : L := (fun u => if u = i then 1 else 0,0)
def hi (i : Var) : L := (fun u => if u = i then -1 else 0,-1)

theorem witnesses : ∀ k : Fin 6,
    (∀ j : Fin 6, (clauseCP (pairClause j)).Holds (point k) ↔ j ≠ k) ∧
    (∀ i : Var, (lo i).Holds (point k) ∧ (hi i).Holds (point k)) ∧ ¬cap.Holds (point k) := by
  unfold CPLine.Holds; decide +kernel

private theorem addH {a : Var → Bool} {e f : L} (h : e.Holds a) (h' : f.Holds a) :
    CPLine.Holds a (e.1+f.1,e.2+f.2) := by
  simp only [CPLine.Holds,Pi.add_apply,add_mul,Finset.sum_add_distrib] at *
  omega

private theorem mulH {a : Var → Bool} {e : L} (k : ℕ) (h : e.Holds a) :
    CPLine.Holds a ((k:ℤ) • e.1,(k:ℤ)*e.2) := by
  change (k:ℤ)*e.2 ≤ ∑ v, ((k:ℤ)*e.1 v)*(if a v then 1 else 0)
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem divH {a : Var → Bool} {e : L} (d : ℕ) (h : e.Holds a) (hd : 0 < d)
    (dv : ∀ v, (d:ℤ) ∣ e.1 v) :
    CPLine.Holds a (fun v => e.1 v/(d:ℤ),-((-e.2)/(d:ℤ))) := by
  let t := ∑ v, (e.1 v/(d:ℤ))*(if a v then (1:ℤ) else 0)
  have prod : (d:ℤ)*t = ∑ v, e.1 v*(if a v then 1 else 0) := by
    simp only [t, Finset.mul_sum, ← mul_assoc, Int.mul_ediv_cancel_of_dvd (dv _)]
  change -((-e.2)/(d:ℤ)) ≤ t
  have le := (Int.le_ediv_iff_mul_le (by exact_mod_cast hd : 0 < (d:ℤ))).mpr
    (show (-t)*(d:ℤ) ≤ -e.2 by
      change e.2 ≤ _ at h
      nlinarith only [prod,h])
  omega

private def Inv (k : Fin 6) (π : List L) : Prop :=
  clauseCP (pairClause k) ∈ π ∨ ∀ e ∈ π, e.Holds (point k)

private theorem advance {k : Fin 6} {π : List L} {e : L} (ih : Inv k π)
    (rule : (∀ f ∈ π, f.Holds (point k)) → e = clauseCP (pairClause k) ∨ e.Holds (point k)) :
    Inv k (e::π) := by
  rcases ih with seen | allH
  · exact .inl (List.mem_cons_of_mem _ seen)
  rcases rule allH with rfl | ok
  · exact .inl List.mem_cons_self
  · exact .inr (fun f hf => (List.mem_cons.mp hf).elim (fun he => he ▸ ok) (allH f))

theorem traceInvariant (k : Fin 6) {π : List L} (h : IsCPDerivation edges π) : Inv k π := by
  induction h with
  | nil => exact .inr (by simp)
  | ax C _ hc ih =>
    obtain ⟨j,rfl⟩ := hc
    apply advance ih
    intro _
    by_cases eq : j=k
    · exact .inl (eq ▸ rfl)
    · exact .inr (((witnesses k).1 j).mpr eq)
  | boolLo p _ ih => exact advance ih (fun _ => .inr (((witnesses k).2.1 p).1))
  | boolHi p _ ih => exact advance ih (fun _ => .inr (((witnesses k).2.1 p).2))
  | add _ he hf ih => exact advance ih (fun allH => .inr (addH (allH _ he) (allH _ hf)))
  | mul d _ he ih => exact advance ih (fun allH => .inr (mulH d (allH _ he)))
  | div d _ he hd dv ih => exact advance ih (fun allH => .inr (divH d (allH _ he) hd dv))

/-- Every official CP trace that derives the four-variable capacity contains all six edge lines. -/
theorem capacityUsesEveryEdge {π : List L} (h : IsCPDerivation edges π) (hc : cap ∈ π)
    (k : Fin 6) : clauseCP (pairClause k) ∈ π :=
  (traceInvariant k h).resolve_right (fun allH => (witnesses k).2.2 (allH _ hc))

theorem sixDistinct : Function.Injective (fun k : Fin 6 => clauseCP (pairClause k)) := by
  intro i j he
  by_contra h
  have hi := ((witnesses i).1 j).mpr (Ne.symm h)
  change clauseCP (pairClause i) = clauseCP (pairClause j) at he
  rw [←he] at hi
  exact ((witnesses i).1 i).mp hi rfl

private theorem allHold {F : Set (Clause Var)} (k : Fin 6) (base : ∀ C ∈ F, (clauseCP C).Holds (point k))
    {π : List L} (h : IsCPDerivation F π) : ∀ e ∈ π, e.Holds (point k) := by
  have keep {e : L} {xs : List L} (head : e.Holds (point k))
      (tail : ∀ f ∈ xs, f.Holds (point k)) : ∀ f ∈ e::xs, f.Holds (point k) :=
    fun f hf => (List.mem_cons.mp hf).elim (fun eq => eq ▸ head) (tail f)
  induction h with
  | nil => simp
  | ax C _ hc ih => exact keep (base C hc) ih
  | boolLo p _ ih => exact keep (((witnesses k).2.1 p).1) ih
  | boolHi p _ ih => exact keep (((witnesses k).2.1 p).2) ih
  | add _ he hf ih => exact keep (addH (ih _ he) (ih _ hf)) ih
  | mul d _ he ih => exact keep (mulH d (ih _ he)) ih
  | div d _ he hd dv ih => exact keep (divH d (ih _ he) hd dv) ih

/-- Even with arbitrary extra Boolean bounds and rounds, deleting any one pair axiom
precludes capacity. Equivalently a subformula deriving capacity must be the full edge set. -/
theorem capacityNeedsFullBasis {F : Set (Clause Var)} (sub : F ⊆ edges) {π : List L}
    (h : IsCPDerivation F π) (hc : cap ∈ π) : F = edges := by
  apply Set.Subset.antisymm sub
  rintro _ ⟨k,rfl⟩
  by_contra missing
  apply (witnesses k).2.2
  apply allHold k _ h _ hc
  intro C hC
  obtain ⟨j,rfl⟩ := sub hC
  apply ((witnesses k).1 j).mpr
  rintro rfl
  exact missing hC

end CliqueEdges
#print axioms CliqueEdges.capacityUsesEveryEdge
#print axioms CliqueEdges.sixDistinct
#print axioms CliqueEdges.capacityNeedsFullBasis
