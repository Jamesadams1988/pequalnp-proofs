import RectanglePlane

namespace Row4201.RectanglePlane
open Row4201.StarBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Edges are disjunctions of two-variable conjunctions, retaining the diagonal
when a rectangle uses the same raw variable as both operands. -/
def fires (s : Finset E) (x : V → Bool) : Prop := ∃ e ∈ s, x e.1 = true ∧ x e.2 = true

def literalTruth (x : V → Bool) : Prop :=
  ∃ a b : V, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ [0,5,7,17,20]) ∧
    x a = true ∧ x b = true

theorem literalSpec (x : V → Bool) : fires target x ↔ literalTruth x := by
  constructor
  · rintro ⟨⟨a,b⟩,ab,ha,hb⟩
    exact ⟨a,b, by simpa [target,oriented] using ab,ha,hb⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    exact ⟨(a,b),by simpa [target,oriented] using ab,ha,hb⟩

private theorem targetStrict {e : E} (he : e ∈ target) : e.1 < e.2 := by
  obtain ⟨a,b⟩ := e
  have h : a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ [0,5,7,17,20] := by
    simpa [target,oriented] using he
  exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le h.1 h.2.1)

private theorem selected {x y u v : V} (xy : x ≤ y) (uv : u < v)
    (l : u=x ∨ u=y) (r : v=x ∨ v=y) : (u,v) = (x,y) := by
  rcases l with rfl | rfl <;> rcases r with rfl | rfl <;> first | rfl | exact (lt_irrefl _ uv).elim | exact (not_lt_of_ge xy uv).elim

private theorem subsetOfTests {a b : Finset E}
    (sorted : ∀ e ∈ a, e.1 ≤ e.2) (strict : ∀ e ∈ b, e.1 < e.2)
    (h : ∀ x : V → Bool, fires a x → fires b x) : a ⊆ b := by
  rintro ⟨u,v⟩ mem
  let x (i : V) : Bool := decide (i=u ∨ i=v)
  have src : fires a x := ⟨(u,v),mem,by simp [x],by simp [x]⟩
  obtain ⟨⟨p,q⟩,pq,hp,hq⟩ := h x src
  have eq := selected (sorted (u,v) mem) (strict (p,q) pq)
    (show p = u ∨ p = v by simpa [x] using hp)
    (show q = u ∨ q = v by simpa [x] using hq)
  exact eq ▸ pq

theorem recoverTarget {s : Finset E} (sorted : ∀ e ∈ s, e.1 ≤ e.2)
    (computes : ∀ x, fires s x ↔ literalTruth x) : s = target := by
  have functional (x) := (computes x).trans (literalSpec x).symm
  have sub := subsetOfTests sorted (fun _ h => targetStrict h) (fun x => (functional x).mp)
  apply Finset.Subset.antisymm sub
  exact subsetOfTests (fun _ h => (targetStrict h).le) (fun _ h => targetStrict (sub h))
    (fun x => (functional x).mpr)

private theorem sortedOutputs {inputs bank : Finset (Finset E)} {o : ℕ} (post : Joins inputs o bank)
    (base : ∀ R ∈ inputs, ∀ e ∈ R, e.1 ≤ e.2) :
    ∀ S ∈ bank, ∀ e ∈ S, e.1 ≤ e.2 := by
  induction post with
  | start => exact base
  | step run a b ih =>
    intro S hs e he
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact (Finset.mem_union.mp he).elim (ih _ a e) (ih _ b e)
    · exact ih _ hs _ he

theorem rectangleFunctionLower {initial inputBank : Finset (Finset V)}
    {products outputBank : Finset (Finset E)} {i o : ℕ} {s : Finset E}
    (seeds : ∀ S ∈ initial, S.card ≤ 1) (pre : Joins initial i inputBank)
    (middle : ∀ R ∈ products, ∃ A ∈ inputBank, ∃ B ∈ inputBank, R = rectangle A B)
    (post : Joins products o outputBank) (output : s ∈ outputBank)
    (computes : ∀ x, fires s x ↔ literalTruth x) : 104 ≤ i+o := by
  have base (R) (hr : R ∈ products) (e) (he : e ∈ R) : e.1 ≤ e.2 := by
    obtain ⟨A,_,B,_,rfl⟩ := middle R hr
    obtain ⟨a,_,hab⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hab
    exact min_le_max
  have eq := recoverTarget (sortedOutputs post base s output) computes
  exact rectangleORLower seeds pre middle post (eq ▸ output)

end Row4201.RectanglePlane
#print axioms Row4201.RectanglePlane.rectangleFunctionLower
