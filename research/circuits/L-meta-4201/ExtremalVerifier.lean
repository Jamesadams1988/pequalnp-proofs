import PEqualNP.Defs

/-! Extremal inputs suffice to check the incidence function of an arbitrary
monotone circuit with the official wire semantics, including out-of-range reads. -/
namespace ExtremalVerifier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev LEbits (s t : List Bool) :=
  List.Forall₂ (fun a b : Bool => a = true → b = true) s t

private theorem readMono {s t : List Bool} (h : LEbits s t) (i : ℕ) :
    s.getD i false = true → t.getD i false = true := by
  induction h generalizing i with
  | nil => simp
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldMono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {s t : List Bool} (h : LEbits s t) : LEbits (gs.foldl step s) (gs.foldl step t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun g' hg => hm g' (List.mem_cons_of_mem _ hg))
    apply List.rel_append h
    apply List.Forall₂.cons _ .nil
    intro he
    rcases hm g List.mem_cons_self with hg | hg <;>
      rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
    · exact fun i hi => readMono h i (he i hi)
    · obtain ⟨i,hi,v⟩ := he
      exact ⟨i,hi,readMono h i v⟩

theorem evalMono {n : ℕ} (C : Circuit) (hm : Monotone2 C) {x y : Fin n → Bool}
    (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply readMono (foldMono C.gates (fun g hg => (hm g hg).1) _) C.output
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hx hy
  simpa [List.get_ofFn] using h ⟨i, by simpa using hx⟩

def input {n : ℕ} (s : Finset (Fin n)) (i : Fin n) := decide (i ∈ s)

def run {n : ℕ} (C : Circuit) (s : Finset (Fin n)) : Bool := C.eval (List.ofFn (input s))

def independent {n : ℕ} (edge : Fin n → Fin n → Prop) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ¬ edge a b

def maximalIndependent {n : ℕ} (edge : Fin n → Fin n → Prop) (s : Finset (Fin n)) : Prop :=
  independent edge s ∧ ∀ t, s ⊆ t → independent edge t → t = s

private theorem extend {n : ℕ} {edge : Fin n → Fin n → Prop} {s : Finset (Fin n)}
    (hs : independent edge s) : ∃ t, s ⊆ t ∧ maximalIndependent edge t := by
  classical
  let pool := Finset.univ.filter (fun t : Finset (Fin n) => s ⊆ t ∧ independent edge t)
  have member {t} : t ∈ pool ↔ s ⊆ t ∧ independent edge t := by simp [pool]
  obtain ⟨t, ht, best⟩ := pool.exists_max_image Finset.card ⟨s,member.mpr ⟨Finset.Subset.rfl,hs⟩⟩
  obtain ⟨st,good⟩ := member.mp ht
  refine ⟨t, st, good, fun u tu hu => ?_⟩
  exact (Finset.eq_of_subset_of_card_le tu (best u (member.mpr ⟨st.trans tu,hu⟩))).symm

theorem edgeAndMaximalTests {n : ℕ} (edge : Fin n → Fin n → Prop)
    (C : Circuit) (hm : Monotone2 C) :
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b, edge a b ∧ x a = true ∧ x b = true) ↔
    (∀ a b, edge a b → run C {a,b} = true) ∧
    (∀ s, maximalIndependent edge s → run C s = false) := by
  classical
  constructor
  · intro all
    constructor
    · intro a b hab
      exact (all _).mpr ⟨a,b,hab,by simp [input],by simp [input]⟩
    · intro s hs
      cases out : run C s with
      | false => rfl
      | true =>
        obtain ⟨a,b,hab,ha,hb⟩ := (all _).mp out
        exact (hs.1 a (of_decide_eq_true ha) b (of_decide_eq_true hb) hab).elim
  · rintro ⟨on,off⟩ x
    constructor
    · intro one
      by_contra missing
      let s := Finset.univ.filter (fun i => x i = true)
      have mem {i} : i ∈ s ↔ x i = true := by simp [s]
      have hs : independent edge s := fun a ha b hb hab =>
        missing ⟨a,b,hab,mem.mp ha,mem.mp hb⟩
      obtain ⟨t,st,ht⟩ := extend hs
      have out : run C t = true := evalMono C hm (fun i h => decide_eq_true (st (mem.mpr h))) one
      rw [off t ht] at out
      contradiction
    · rintro ⟨a,b,hab,ha,hb⟩
      apply evalMono C hm (x := input {a,b}) _ (on a b hab)
      intro i hi
      rcases (by simpa [input] using hi : i = a ∨ i = b) with rfl | rfl <;> assumption

end ExtremalVerifier

#print axioms ExtremalVerifier.edgeAndMaximalTests
