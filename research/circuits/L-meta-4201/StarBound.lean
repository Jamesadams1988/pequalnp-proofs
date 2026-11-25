import PEqualNP.Defs

/-! Binary OR circuits with shared intermediate wires, arbitrary incident star
products, and an arbitrary shared outer OR circuit. Each input can index a star
on either side of the bipartition. Rectangles may overlap. -/
namespace Row4201.StarBound

/-- A bank retains all previous wires. A step adds one binary OR of prior wires.
Wires denote sets, so their OR is union. Repeated operands and dead gates are allowed. -/
inductive Joins {α : Type} [DecidableEq α] (initial : Finset (Finset α)) :
    ℕ → Finset (Finset α) → Prop
  | start : Joins initial 0 initial
  | step {k B a b} : Joins initial k B → a ∈ B → b ∈ B →
      Joins initial (k+1) (insert (a∪b) B)

def almost {β : Type} [DecidableEq β] (S P : Finset β) : Prop := (S \ P).card ≤ 1

private theorem mono {β : Type} [DecidableEq β] {S P Q : Finset β} (h : almost S P)
    (sub : P ⊆ Q) : almost S Q := by
  apply le_trans (Finset.card_le_card ?_) h
  intro e he
  obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr ⟨hs,fun hp => hn (sub hp)⟩

private theorem small {β : Type} [DecidableEq β] (S P : Finset β) (h : S.card ≤ 1) : almost S P :=
  (Finset.card_le_card Finset.sdiff_subset).trans h

/-- Paying for the unaccounted elements in the first operand costs at most one.
Any unaccounted element of the union must then come from the second operand. -/
theorem repair {β : Type} [DecidableEq β] {A B P : Finset β} (a : almost A P) (b : almost B P) :
    ∃ Q : Finset β, P ⊆ Q ∧ Q.card ≤ P.card+1 ∧ almost (A ∪ B) Q := by
  let Q := P ∪ (A \ P)
  refine ⟨Q, Finset.subset_union_left, (Finset.card_union_le ..).trans (Nat.add_le_add_left a _), ?_⟩
  apply le_trans (Finset.card_le_card ?_) b
  intro e he
  simp only [Q, Finset.mem_sdiff, Finset.mem_union] at he ⊢
  tauto

/-- The outer OR aggregation counts each operation once, regardless of fan-out. -/
theorem outer {β : Type} [DecidableEq β] {initial bank : Finset (Finset β)} {k : ℕ}
    (run : Joins initial k bank) {P : Finset β} (base : ∀ S ∈ initial, almost S P) :
    ∃ Q : Finset β, Q.card ≤ P.card+k ∧ ∀ S ∈ bank, almost S Q := by
  induction run with
  | start => exact ⟨P, by omega, base⟩
  | @step k B a b run ha hb ih =>
    obtain ⟨old, budget, ok⟩ := ih
    obtain ⟨new, extendsOld, addition, joined⟩ := repair (ok a ha) (ok b hb)
    refine ⟨new, by omega, ?_⟩
    intro S hs
    rcases Finset.mem_insert.mp hs with rfl | prior
    · exact joined
    · exact mono (ok _ prior) extendsOld

/-- For each inner wire and every possible center whose neighborhood contains
it, all but one of its represented incidence edges are paid for. A wire with
at least two independent leaves has at most one such center. -/
theorem inner {α β : Type} [DecidableEq α] [DecidableEq β]
    (neighbors : α → Finset α) (edge : α → α → β)
    (thin : ∀ c d : α, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1)
    {initial bank : Finset (Finset α)} {k : ℕ}
    (seeds : ∀ S ∈ initial, S.card ≤ 1) (run : Joins initial k bank) :
    ∃ P : Finset β, P.card ≤ k ∧ ∀ S ∈ bank, ∀ c, S ⊆ neighbors c → almost (S.image (edge c)) P := by
  induction run with
  | start =>
    refine ⟨∅,by simp,fun S hs c _ => small _ _ (Finset.card_image_le.trans (seeds _ hs))⟩
  | @step k B A D run ha hd ih =>
    obtain ⟨P, budget, ok⟩ := ih
    by_cases more : 1 < (A ∪ D).card
    · by_cases admitted : ∃ c, (A ∪ D) ⊆ neighbors c
      · obtain ⟨c, hc⟩ := admitted
        have ha' := ok A ha c (Finset.subset_union_left.trans hc)
        have hd' := ok D hd c (Finset.subset_union_right.trans hc)
        obtain ⟨Q,le,sz,both⟩ := repair ha' hd'
        refine ⟨Q,by omega,?_⟩
        intro S hs d hS
        rcases Finset.mem_insert.mp hs with rfl | old
        · have same : d = c := by
            by_contra ne
            have sub : A ∪ D ⊆ neighbors d ∩ neighbors c := fun z hz =>
              Finset.mem_inter.mpr ⟨hS hz,hc hz⟩
            have ub := (Finset.card_le_card sub).trans (thin d c ne)
            omega
          simpa [same,Finset.image_union] using both
        · exact mono (ok S old d hS) le
      · refine ⟨P,by omega,?_⟩
        intro S hs c hS
        rcases Finset.mem_insert.mp hs with rfl | old
        · exact (admitted ⟨c,hS⟩).elim
        · exact ok S old c hS
    · refine ⟨P,by omega,?_⟩
      intro S hs c hS
      rcases Finset.mem_insert.mp hs with rfl | old
      · exact small _ _ (Finset.card_image_le.trans (by omega))
      · exact ok S old c hS

/-- Input unions, followed by any number of stars, followed by output unions.
The shared inner and outer gates together number at least |target|−1. -/
theorem starBound {α β : Type} [DecidableEq α] [DecidableEq β]
    (neighbors : α → Finset α) (edge : α → α → β)
    (thin : ∀ c d : α, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1)
    {initial inputBank : Finset (Finset α)} {stars outputBank : Finset (Finset β)}
    {i o : ℕ} {target : Finset β}
    (inputs : ∀ S ∈ initial, S.card ≤ 1)
    (inputRun : Joins initial i inputBank)
    (products : ∀ R ∈ stars, ∃ S ∈ inputBank, ∃ c, S ⊆ neighbors c ∧ R = S.image (edge c))
    (outputRun : Joins stars o outputBank) (computes : target ∈ outputBank) :
    target.card ≤ i + o + 1 := by
  obtain ⟨P,hP,ok⟩ := inner neighbors edge thin inputs inputRun
  have paid (R) (hr : R ∈ stars) : almost R P := by
    obtain ⟨S,hs,c,sub,rfl⟩ := products R hr
    exact ok S hs c sub
  obtain ⟨Q,hQ,done⟩ := outer outputRun paid
  have residual := done target computes
  have sub : target ⊆ Q ∪ (target \ Q) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have total := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  unfold almost at residual
  omega

end Row4201.StarBound
#print axioms Row4201.StarBound.starBound
