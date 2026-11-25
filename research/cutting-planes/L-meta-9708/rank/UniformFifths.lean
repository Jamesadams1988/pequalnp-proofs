import Mathlib
/-! The arithmetic part of the rank-two uniform-fifths argument. All weights
are row-normalized nonnegative integers. A ceiling loss of at most two in
denominator-three numerators is allowed. -/
namespace UniformFifths

abbrev R := Fin 5 → ℕ
abbrev T := Fin 10

def triple : T → Fin 3 → Fin 5 := ![
  ![0,1,2], ![0,1,3], ![0,1,4], ![0,2,3], ![0,2,4],
  ![0,3,4], ![1,2,3], ![1,2,4], ![1,3,4], ![2,3,4]]

def total (r : R) := r 0 + r 1 + r 2 + r 3 + r 4
def score (r : R) (t : T) := r (triple t 0) + r (triple t 1) + r (triple t 2)

theorem triple_injective : ∀ t, Function.Injective (triple t) := by decide +kernel

private theorem four_support (r : R) (zero : ∃ j, r j = 0) :
    ∃ t, 3*total r ≤ 4*score r t := by
  obtain ⟨j,hj⟩ := zero
  by_contra! h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9
  simp [score,triple,total] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  fin_cases j <;> simp_all <;> omega

private theorem binary_small (r : R) (bound : ∀ h, r h ≤ 1) (small : total r ≤ 3) :
    ∃ t, total r ≤ score r t := by
  by_contra! h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9
  have b0 := bound 0; have b1 := bound 1; have b2 := bound 2
  have b3 := bound 3; have b4 := bound 4
  simp [score,triple,total] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 small
  omega

private theorem binary_four_avoids (r : R) (bound : ∀ h, r h ≤ 1)
    (four : 4 ≤ total r) (h : Fin 5) :
    ∃ t, (∀ j, triple t j ≠ h) ∧ 3 ≤ score r t := by
  have b0 := bound 0; have b1 := bound 1; have b2 := bound 2
  have b3 := bound 3; have b4 := bound 4
  simp [total] at four
  fin_cases h <;> by_contra! hh
  all_goals
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2; have h3 := hh 3
    have h4 := hh 4; have h5 := hh 5; have h6 := hh 6; have h7 := hh 7
    have h8 := hh 8; have h9 := hh 9
    simp [score,triple,Fin.forall_fin_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    omega

private theorem weighted_rows {m : ℕ} (r : Fin m → R) (zero : ∀ i, ∃ h, r i h = 0)
    (B : ℕ) (triples : ∀ f : Fin m → T, (∑ i, score (r i) (f i)) ≤ 3*B+2) :
    3*(∑ i, total (r i)) ≤ 4*(3*B+2) := by
  choose f hf using fun i => four_support (r i) (zero i)
  have s := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
  simpa only [← Finset.mul_sum] using s.trans
    (by simpa only [← Finset.mul_sum] using Nat.mul_le_mul_left 4 (triples f))

/-- Ordinary rowwise triples and a pinned row followed by triples certify each
second-round integer upper objective at the uniform fifths point. The two
pinned inequalities keep only one or two nonnegative row contributions. -/
theorem normalized_fifths {m : ℕ} (r : Fin m → R) (zero : ∀ i, ∃ h, r i h = 0)
    (B : ℕ) (triples : ∀ f : Fin m → T, (∑ i, score (r i) (f i)) ≤ 3*B+2)
    (pin : ∀ i h, 3*r i h ≤ 3*B+2)
    (double : ∀ i k : Fin m, i ≠ k → ∀ h t, (∀ j, triple t j ≠ h) →
      3*r i h + score (r k) t ≤ 3*B+2) :
    (∑ i, total (r i)) ≤ 5*B := by
  have rough := weighted_rows r zero B triples
  by_contra! bad
  have Bsmall : B ≤ 1 := by omega
  cases B with
  | zero =>
    have rz (i h) : r i h = 0 := by have := pin i h; omega
    simp [total,rz] at bad
  | succ B =>
    have bz : B = 0 := by omega
    subst B
    have exactly : (∑ i, total (r i)) = 6 := by omega
    have unit (i h) : r i h ≤ 1 := by have := pin i h; omega
    by_cases hs : ∀ i, total (r i) ≤ 3
    · choose f hf using fun i => binary_small (r i) (unit i) (hs i)
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
      have := triples f
      omega
    · push Not at hs
      obtain ⟨k,hk⟩ := hs
      have cap (i) : total (r i) ≤ 5 := by
        have h0 := unit i 0; have h1 := unit i 1; have h2 := unit i 2
        have h3 := unit i 3; have h4 := unit i 4
        unfold total; omega
      have extra : ∃ i : Fin m, i ≠ k ∧ ∃ h, 0 < r i h := by
        by_contra! no
        have lone : (∑ i, total (r i)) = total (r k) := by
          apply Finset.sum_eq_single k
          · intro i hi ne
            have hz (h) : r i h = 0 := Nat.eq_zero_of_le_zero (no i ne h)
            simp [total,hz]
          · simp
        have := cap k
        omega
      obtain ⟨i,ne,h,pos⟩ := extra
      obtain ⟨t,avoid,big⟩ := binary_four_avoids (r k) (unit k) (by omega) h
      have := double i k ne h t avoid
      omega

def intScore (a : Fin 5 → ℤ) (t : T) : ℤ :=
  a (triple t 0) + a (triple t 1) + a (triple t 2)

private theorem denominator_three {b d z : ℤ} (hd : 0 < d) (h : d*z ≤ 3*b) :
    z ≤ 3*(b/d)+2 := by
  by_contra! fail
  have lo : 3*(b/d)+3 ≤ z := by omega
  have pressure := mul_le_mul_of_nonneg_left lo hd.le
  have top := Int.lt_mul_ediv_self_add (x := b) hd
  nlinarith only [h,pressure,top]

private theorem avoiding (h : Fin 5) : ∃ t, ∀ j, triple t j ≠ h := by
  revert h; decide +kernel

/-- The ordinary and pinned denominator-three witness tests on signed integer
objectives imply the true rounded, uniform-fifths inequality. -/
theorem signed_fifths {m : ℕ} (a : Fin m → Fin 5 → ℤ) (b d : ℤ) (hd : 0 < d)
    (triples : ∀ f : Fin m → T, d*(∑ i, intScore (a i) (f i)) ≤ 3*b)
    (pinned : ∀ (p : Fin m) (h : Fin 5) (f : Fin m → T),
      (∀ i, i ≠ p → ∀ j, triple (f i) j ≠ h) →
      d*(∑ i, if i = p then 3*a i h else intScore (a i) (f i)) ≤ 3*b) :
    (∑ i, ∑ j, a i j) ≤ 5*(b/d) := by
  classical
  have rowMin (i : Fin m) : ∃ z : Fin 5, ∀ h, a i z ≤ a i h := by
    obtain ⟨z,_,hz⟩ := Finset.exists_min_image Finset.univ (a i) Finset.univ_nonempty
    exact ⟨z,fun h => hz h (Finset.mem_univ _)⟩
  choose z hz using rowMin
  let u (i : Fin m) := a i (z i)
  let r (i : Fin m) (h : Fin 5) := (a i h - u i).toNat
  have repr (i h) : a i h = (r i h : ℤ) + u i := by
    have le := hz i h
    simp [r,u,Int.toNat_of_nonneg (sub_nonneg.mpr le)]
  have zero (i) : ∃ h, r i h = 0 := ⟨z i, by simp [r,u]⟩
  have sc (i t) : intScore (a i) t = (score (r i) t : ℤ) + 3*u i := by
    simp only [intScore,score,Nat.cast_add,repr i]; ring
  let limit := b/d - ∑ i, u i
  have tripleBound (f : Fin m → T) :
      ((∑ i, score (r i) (f i) : ℕ) : ℤ) ≤ 3*limit+2 := by
    have e := denominator_three hd (triples f)
    simp only [sc, Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_sum] at *
    dsimp [limit]; omega
  have nn : 0 ≤ limit := by
    have e := tripleBound (fun _ => 0)
    have nonneg : 0 ≤ ((∑ i, score (r i) 0 : ℕ) : ℤ) := by positivity
    omega
  let B := limit.toNat
  have Bcast : (B : ℤ) = limit := Int.toNat_of_nonneg nn
  have nt (f : Fin m → T) : (∑ i, score (r i) (f i)) ≤ 3*B+2 := by
    exact_mod_cast (show ((∑ i, score (r i) (f i) : ℕ) : ℤ) ≤ 3*(B : ℤ)+2 by
      simpa only [Bcast] using tripleBound f)
  have pinBound (p h) (f : Fin m → T) (avoid : ∀ i, i ≠ p → ∀ j, triple (f i) j ≠ h) :
      (∑ i, if i = p then 3*r i h else score (r i) (f i)) ≤ 3*B+2 := by
    have e := denominator_three hd (pinned p h f avoid)
    have eq (i : Fin m) :
        (if i = p then 3*a i h else intScore (a i) (f i)) =
        ((if i = p then 3*r i h else score (r i) (f i) : ℕ) : ℤ) + 3*u i := by
      by_cases hi : i = p
      · simp only [ite_eq_left hi,Nat.cast_mul,Nat.cast_ofNat,repr i h]; ring
      · simp [hi,sc]
    simp only [eq,Finset.sum_add_distrib,← Finset.mul_sum,← Nat.cast_sum] at e
    have cert : ((∑ i, if i = p then 3*r i h else score (r i) (f i) : ℕ) : ℤ) ≤
        3*(B : ℤ)+2 := by
      rw [Bcast]
      dsimp [limit]; omega
    exact_mod_cast cert
  have one (p h) : 3*r p h ≤ 3*B+2 := by
    obtain ⟨t,ht⟩ := avoiding h
    let val (i : Fin m) := if i = p then 3*r i h else score (r i) t
    have lim : (∑ i, val i) ≤ 3*B+2 := pinBound p h (fun _ => t) (fun _ _ => ht)
    have vip := Finset.single_le_sum (f := val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
    simpa [val] using vip.trans lim
  have two (p k : Fin m) (ne : p ≠ k) (h t) (ht : ∀ j, triple t j ≠ h) :
      3*r p h + score (r k) t ≤ 3*B+2 := by
    let val (i : Fin m) := if i = p then 3*r i h else score (r i) t
    have lim : (∑ i, val i) ≤ 3*B+2 := pinBound p h (fun _ => t) (fun _ _ => ht)
    have hdub : (∑ i ∈ ({p,k} : Finset (Fin m)), val i) ≤ ∑ i, val i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa [val,ne,Ne.symm ne] using hdub.trans lim
  have result := normalized_fifths r zero B nt one two
  have finish (i) : (∑ j, a i j) = (total (r i) : ℤ) + 5*u i := by
    simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one,repr i,total,Nat.cast_add]
    norm_num
    ring
  simp only [finish,Finset.sum_add_distrib,← Finset.mul_sum,← Nat.cast_sum]
  have ri : ((∑ i, total (r i) : ℕ) : ℤ) ≤ 5*(B : ℤ) := by exact_mod_cast result
  rw [Bcast] at ri
  dsimp [limit] at ri
  omega

end UniformFifths
#print axioms UniformFifths.signed_fifths
