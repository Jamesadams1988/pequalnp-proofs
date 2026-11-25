import GlobalRank

/-! The division formula in this file is the one in IsCPDerivation.div.
A rank-one line allows arbitrary additions and nonnegative multiplications
before and after a division. A division may use only an unrounded parent. -/
namespace PHPThird.CP
open PEqualNP.Search PEqualNP.ProofComplexity
abbrev V4 := V 4
abbrev Line := CPLine V4

def holdsAt (den : ℤ) (x : V4 → ℤ) (e : Line) : Prop := den*e.2 ≤ ∑ v, e.1 v*x v
def rawValid (e : Line) := ∀ x : V4 → ℤ, Feasible x → holdsAt 2 x e
def third (e : Line) := holdsAt 3 (fun _ => 1) e
def plus (e f : Line) : Line := (e.1+f.1,e.2+f.2)
def times (k : ℕ) (e : Line) : Line := ((k:ℤ) • e.1,(k:ℤ)*e.2)
def divide (d : ℕ) (e : Line) : Line := (fun v => e.1 v/(d:ℤ),-((-e.2)/(d:ℤ)))

inductive Linear (seed : Set Line) : Line → Prop
  | start {e} : e ∈ seed → Linear seed e
  | add {e f} : Linear seed e → Linear seed f → Linear seed (plus e f)
  | mul (k : ℕ) {e} : Linear seed e → Linear seed (times k e)

theorem linearSound {seed : Set Line} {den x} (base : ∀ e ∈ seed, holdsAt den x e)
    {e} (h : Linear seed e) : holdsAt den x e := by
  induction h with
  | start hs => exact base _ hs
  | add _ _ h j =>
    simp only [holdsAt,plus, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at *
    omega
  | @mul k e _ h =>
    change den*((k:ℤ)*e.2) ≤ ∑ v, ((k:ℤ)*e.1 v)*x v
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [mul_left_comm den (k:ℤ)]
    exact mul_le_mul_of_nonneg_left h (by positivity)

def unit (p v : V4) : ℤ := if p=v then 1 else 0

inductive Axiom : Line → Prop
  | clause {C} : C ∈ PHP 4 3 → Axiom (clauseCP C)
  | lo (p : V4) : Axiom (fun u => if u=p then 1 else 0, 0)
  | hi (p : V4) : Axiom (fun u => if u=p then -1 else 0, -1)

private theorem pigShape : ∀ i : Fin 4,
    clauseCP (Finset.univ.image (fun j : Fin 3 => ((i,j),true))) =
      ((fun v : V4 => if v.1 = i then (1:ℤ) else 0),1) := by decide +kernel

private theorem edgeShape : ∀ i k : Fin 4, ∀ j : Fin 3, i ≠ k →
    clauseCP {((i,j),false),((k,j),false)} =
      ((fun v : V4 => -unit (i,j) v - unit (k,j) v),-1) := by decide +kernel

private theorem dotUnit (p : V4) (x : V4 → ℤ) : (∑ v, unit p v*x v) = x p := by
  simp [unit,ite_mul]

theorem axiomRaw {e} (h : Axiom e) : rawValid e := by
  intro x hx
  cases h with
  | clause mem =>
    rcases mem with ⟨i,rfl⟩ | ⟨i,k,j,ne,rfl⟩
    · rw [pigShape]
      change 2*1 ≤ ∑ v, (if v.1 = i then (1:ℤ) else 0)*x v
      rw [Fintype.sum_prod_type]
      change 2*1 ≤ ∑ k : Fin 4, ∑ j : Fin 3, (if k=i then (1:ℤ) else 0)*x (k,j)
      simp [hx.2.1 i]
    · rw [edgeShape i k j ne]
      simp only [holdsAt, sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        dotUnit, mul_neg, mul_one]
      have := hx.2.2 i k j ne
      omega
  | lo p => simpa [holdsAt, ite_mul] using (hx.1 p).1
  | hi p => simpa [holdsAt, ite_mul] using (neg_le_neg (hx.1 p).2)

theorem divideThird {e : Line} (raw : rawValid e) (d : ℕ) (hd : 0 < d)
    (dvd : ∀ v, (d:ℤ) ∣ e.1 v) : third (divide d e) := by
  let a (v : V4) := -(e.1 v / (d:ℤ))
  have eq (v : V4) : (d:ℤ)*a v = -e.1 v := by
    simp only [a,mul_neg,Int.mul_ediv_cancel_of_dvd (dvd v)]
  have ok (w : V4 → ℤ) (hw : Feasible w) :
      (d:ℤ)*(∑ v, a v*w v) ≤ 2*(-e.2) := by
    rw [Finset.mul_sum]
    simp only [← mul_assoc,eq,neg_mul,Finset.sum_neg_distrib,mul_neg,neg_le_neg_iff]
    exact raw _ hw
  have h := globalRoundThird a (-e.2) (d:ℤ) (by exact_mod_cast hd) ok
  simp only [a,Finset.sum_neg_distrib] at h
  simp only [third, holdsAt, divide, mul_one]
  linarith only [h]

abbrev Unrounded := Linear {e | Axiom e}

def FirstCuts : Set Line := {e | Unrounded e ∨
  ∃ p, ∃ d : ℕ, Unrounded p ∧ 0 < d ∧ (∀ v, (d:ℤ) ∣ p.1 v) ∧ e = divide d p}

abbrev FirstClosure := Linear FirstCuts

theorem rawSound {e : Line} (h : Unrounded e) : rawValid e :=
  fun w hw => linearSound (fun _ he => axiomRaw he w hw) h

theorem firstClosureSound {e : Line} (h : FirstClosure e) : third e := by
  apply linearSound (e := e) _ h
  rintro f (hh | ⟨p,d,hp,hd,divides,rfl⟩)
  · have c := divideThird (rawSound hh) 1 (by decide) (by simp)
    simpa [divide, third, holdsAt] using c
  · exact divideThird (rawSound hp) d hd divides

theorem noRankOneRefutation : ¬ FirstClosure ((0 : V4 → ℤ),1) := by
  intro h
  have hf := firstClosureSound h
  simp [third,holdsAt] at hf

end PHPThird.CP
#print axioms PHPThird.CP.noRankOneRefutation
