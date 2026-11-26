import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

/-!
# Conjunctions of factors with an ignored variable

Research credit: James Adams.

A Boolean input is represented by its set of true variables. For a monotone
predicate on a finite input set, a conjunction of at most `k` proper-support
factors exists exactly when at most `k` vertices meet all maximal false supports.
The factors in the forward implication are arbitrary predicates. The converse
uses the positive cofactors and hence supplies monotone factors.
-/

namespace FactorTransversal

variable {V : Type*} [DecidableEq V]

/-- Setting the coordinate to true leaves the value unchanged. -/
def Ignores (g : Finset V → Prop) (v : V) : Prop :=
  ∀ x, g (insert v x) ↔ g x

/-- A false input for which setting any additional coordinate makes it true. -/
def MaximalFalse (F : Finset V → Prop) (m : Finset V) : Prop :=
  ¬ F m ∧ ∀ v, v ∉ m → F (insert v m)

/-- The chosen vertices meet the true-coordinate set of every maximal false input. -/
def HitsMaximalFalse (F : Finset V → Prop) (s : Finset V) : Prop :=
  ∀ m, MaximalFalse F m → ∃ v ∈ s, v ∈ m

/-- A conjunction of at most `k` factors, each independent of some coordinate. -/
def HasSmallConjunction (F : Finset V → Prop) (k : ℕ) : Prop :=
  ∃ n ≤ k, ∃ g : Fin n → Finset V → Prop,
    (∀ i, ∃ v, Ignores (g i) v) ∧ (∀ x, F x ↔ ∀ i, g i x)

/-- Every false input on a finite variable set extends to a maximal false input. -/
theorem exists_maximalFalse_extension [Fintype V] {F : Finset V → Prop}
    {x : Finset V} (hx : ¬ F x) : ∃ m, x ⊆ m ∧ MaximalFalse F m := by
  classical
  let candidates := Finset.univ.filter (fun m : Finset V => x ⊆ m ∧ ¬ F m)
  have mem_iff (m : Finset V) : m ∈ candidates ↔ x ⊆ m ∧ ¬ F m := by
    simp [candidates]
  have hx' : x ∈ candidates := (mem_iff x).2 ⟨fun _ h => h, hx⟩
  obtain ⟨m, hm, hmax⟩ := candidates.exists_max_image Finset.card ⟨x, hx'⟩
  obtain ⟨hxm, hmF⟩ := (mem_iff m).1 hm
  refine ⟨m, hxm, hmF, ?_⟩
  intro v hv
  by_contra hf
  have hnew : insert v m ∈ candidates :=
    (mem_iff _).2 ⟨fun _ hi => Finset.mem_insert_of_mem (hxm hi), hf⟩
  have hle := hmax _ hnew
  rw [Finset.card_insert_of_notMem hv] at hle
  exact Nat.not_succ_le_self _ hle

/-- One ignored coordinate per factor suffices to hit all maximal false inputs. -/
theorem transversal_of_conjunction {F : Finset V → Prop} {k : ℕ}
    (h : HasSmallConjunction F k) :
    ∃ s : Finset V, s.card ≤ k ∧ HitsMaximalFalse F s := by
  classical
  obtain ⟨n, hnk, g, hg, hF⟩ := h
  choose v hv using hg
  let s := Finset.univ.image v
  have hs : s.card ≤ n := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := v))
  refine ⟨s, hs.trans hnk, ?_⟩
  intro m hm
  have hreject : ¬ ∀ i, g i m := fun hall => hm.1 ((hF m).2 hall)
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hreject
  refine ⟨v i, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  by_contra hout
  exact hi ((hv i m).1 ((hF _).1 (hm.2 _ hout) i))

/-- The positive cofactor at `v` is independent of `v`. -/
theorem cofactor_ignores (F : Finset V → Prop) (v : V) :
    Ignores (fun x => F (insert v x)) v := by
  intro x
  simp

/-- A transversal gives a canonical conjunctive representation by positive cofactors. -/
theorem cofactor_conjunction [Fintype V] {F : Finset V → Prop}
    (hmono : Monotone F) {s : Finset V} (hs : HitsMaximalFalse F s) (x : Finset V) :
    F x ↔ ∀ v ∈ s, F (insert v x) := by
  constructor
  · intro hx v _
    exact hmono (Finset.subset_insert v x) hx
  · intro hall
    by_contra hx
    obtain ⟨m, hxm, hm⟩ := exists_maximalFalse_extension hx
    obtain ⟨v, hvs, hvm⟩ := hs m hm
    exact hm.1 (hmono (Finset.insert_subset hvm hxm) (hall v hvs))

/-- The exact factor budget equals the hitting-set budget, including budget zero. -/
theorem conjunction_iff_transversal [Fintype V] {F : Finset V → Prop}
    (hmono : Monotone F) (k : ℕ) :
    HasSmallConjunction F k ↔ ∃ s : Finset V, s.card ≤ k ∧ HitsMaximalFalse F s := by
  refine ⟨transversal_of_conjunction, ?_⟩
  rintro ⟨s, hsk, hs⟩
  let e := s.equivFin
  refine ⟨s.card, hsk, fun i x => F (insert (e.symm i).val x), ?_, ?_⟩
  · intro i
    exact ⟨(e.symm i).val, cofactor_ignores F _⟩
  · intro x
    rw [cofactor_conjunction hmono hs x]
    constructor
    · intro hall i
      exact hall _ (e.symm i).property
    · intro hall v hv
      simpa using hall (e ⟨v, hv⟩)

end FactorTransversal
