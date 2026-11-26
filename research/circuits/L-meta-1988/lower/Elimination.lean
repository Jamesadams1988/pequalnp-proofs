import PEqualNP.MetaComplexity.Helpers.PermInputs

/-! Gate elimination specializes James Adams’s L-meta-9769 Terminal51 certificate to this plane. -/
namespace Plane1988.Elimination
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs
abbrev V := Fin 26
def edges : List (V × V) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
def target (x : V → Bool) := edges.any fun e => x e.1 && x e.2

def rank : V → ℕ := ![16, 5, 15, 3, 7, 0, 16, 11, 1, 13, 16, 16, 2, 8, 4, 16, 16, 16, 12, 9, 16, 14, 6, 16, 10, 16]
def chosen : Fin 16 → V := ![5, 8, 12, 3, 14, 1, 22, 4, 13, 19, 24, 7, 18, 9, 21, 2]
def flexible (i : V) : Bool := decide (i ∈ ({5,8,12,3,4,2} : Finset V))
def witness : Fin 17 → V → V := ![
  ![13, 13, 14, 13, 18, 17, 16, 15, 14, 13, 16, 15, 14, 0, 0, 1, 0, 5, 4, 3, 2, 1, 0, 3, 2, 1],
  ![13, 13, 14, 13, 18, 0, 16, 15, 14, 13, 16, 15, 14, 0, 0, 1, 0, 9, 4, 3, 2, 1, 0, 3, 2, 1],
  ![13, 13, 20, 13, 23, 0, 16, 15, 0, 13, 16, 15, 15, 0, 0, 1, 0, 9, 4, 3, 2, 1, 0, 3, 2, 1],
  ![13, 13, 20, 13, 25, 0, 16, 20, 0, 13, 16, 16, 0, 0, 0, 1, 0, 9, 4, 3, 2, 1, 0, 3, 2, 1],
  ![16, 25, 20, 0, 25, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 1, 0, 9, 4, 7, 2, 1, 0, 4, 2, 1],
  ![16, 25, 20, 0, 25, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 1, 0, 9, 4, 7, 2, 1, 0, 4, 2, 1],
  ![16, 0, 20, 0, 25, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 4, 7, 2, 6, 0, 4, 2, 2],
  ![16, 0, 20, 0, 25, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 4, 7, 2, 6, 0, 4, 2, 2],
  ![16, 0, 20, 0, 0, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 9, 7, 2, 6, 0, 6, 2, 2],
  ![16, 0, 20, 0, 0, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 9, 7, 2, 6, 0, 6, 2, 2],
  ![16, 0, 20, 0, 0, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 9, 0, 2, 6, 0, 6, 2, 2],
  ![16, 0, 20, 0, 0, 0, 16, 20, 0, 20, 16, 16, 0, 0, 0, 7, 0, 9, 9, 0, 2, 6, 0, 6, 0, 2],
  ![16, 0, 20, 0, 0, 0, 16, 0, 0, 20, 16, 16, 0, 0, 0, 11, 0, 9, 9, 0, 2, 6, 0, 6, 0, 2],
  ![16, 0, 20, 0, 0, 0, 16, 0, 0, 20, 16, 16, 0, 0, 0, 11, 0, 9, 0, 0, 2, 6, 0, 6, 0, 2],
  ![16, 0, 20, 0, 0, 0, 16, 0, 0, 0, 16, 16, 0, 0, 0, 11, 0, 10, 0, 0, 2, 6, 0, 6, 0, 2],
  ![16, 0, 20, 0, 0, 0, 16, 0, 0, 0, 16, 16, 0, 0, 0, 11, 0, 10, 0, 0, 2, 0, 0, 6, 0, 2],
  ![16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 16, 0, 0, 0, 11, 0, 10, 0, 0, 6, 0, 0, 6, 0, 10]]

def overlay (t : ℕ) (b x : V → Bool) (i : V) : Bool := if rank i < t then (flexible i && b i) else x i

def pinned (t : ℕ) (b x : V → Bool) := target (overlay t b x)

def low (t : Fin 17) (i j : V) : Bool := decide (j = witness t i)

set_option maxHeartbeats 8000000 in
theorem tests : ∀ t : Fin 17, ∀ i : V, t.val ≤ rank i →
    low t i i = false ∧ target (overlay t.val (fun _ => true) (low t i)) = false ∧
    target (overlay t.val (fun _ => false) (Function.update (low t i) i true)) = true := by decide +kernel

theorem ranks : ∀ t : Fin 16, ∀ i : V, rank i = t.val ↔ i = chosen t := by decide +kernel

theorem monotoneTarget {x y : V → Bool} (h : ∀ i, x i = true → y i = true) : target x = true → target y = true := by
  intro hx
  obtain ⟨e,he,hb⟩ := List.any_eq_true.mp hx
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hb
  exact List.any_eq_true.mpr ⟨e,he,Bool.and_eq_true_iff.mpr ⟨h _ a,h _ b⟩⟩

theorem depends (t : Fin 17) (b : V → Bool) (i : V) (live : t.val ≤ rank i) :
    ∃ x, pinned t.val b (Function.update x i (!x i)) ≠ pinned t.val b x := by
  refine ⟨low t i, ?_⟩
  obtain ⟨atI,lo,hi⟩ := tests t i live
  have hif : pinned t.val b (Function.update (low t i) i true) = true :=
    monotoneTarget (fun j => by unfold overlay; split <;> simp) hi
  have lof : pinned t.val b (low t i) ≠ true := fun l => by
    have : target (overlay t.val (fun _ => true) (low t i)) = true := monotoneTarget (x := overlay t.val b (low t i)) (fun j => by unfold overlay; split <;> simp; tauto) l
    exact Bool.noConfusion (this.symm.trans lo)
  rw [atI]; simp only [Bool.not_false,hif]
  exact Ne.symm lof

theorem pinNext (t : Fin 16) (b : V → Bool) (v : Bool) (ok : (flexible (chosen t) && v) = v) :
    (fun x => pinned t.val b (Function.update x (chosen t) v)) = pinned (t.val+1) (Function.update b (chosen t) v) := by
  funext x
  unfold pinned
  congr 1
  funext i
  have eq := ranks t i
  by_cases hi : i = chosen t
  · subst i
    have h := eq.mpr rfl
    simp [overlay,h,ok]
  · have h := not_iff_not.mpr eq |>.mpr hi
    have iff : rank i < t.val+1 ↔ rank i < t.val := by omega
    simp [overlay,iff,Function.update_of_ne hi]

theorem liveCard : (Finset.univ.filter fun i : V => 16 ≤ rank i).card = 10 := by decide +kernel

theorem pin_fixed (n : ℕ) (f : (Fin (n+1) → Bool) → Bool) (p : Fin (n+1))
    (b : Bool) (s : ℕ)
    (hdep : ∃ x, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n+1) f (s+1)) :
    HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s+1) := relabel_size (⇑σ) f (s+1) h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

def extra : ℕ → ℕ
  | 0 => 0
  | d+1 => extra d + if h : 16-(d+1)<16 then
      (if flexible (chosen ⟨16-(d+1),h⟩) then 2 else 1) else 0

theorem terminalReserve (t : Fin 17) (b : V → Bool) (s : ℕ) (h : HasCircuitSize 26 (pinned t.val b) s) :
    9 ≤ s := by
  have h' := dep_lower_set 26 (pinned t.val b) (Finset.univ.filter fun i : V => 16 ≤ rank i)
    (fun i hi => depends t b i (by have := (Finset.mem_filter.mp hi).2; omega)) s h
  rw [liveCard] at h'
  omega

theorem inductiveBound (d : ℕ) (hd : d ≤ 16) (b : V → Bool) (s : ℕ)
    (hs : HasCircuitSize 26 (pinned (16-d) b) s) : 9 + extra d ≤ s := by
  induction d generalizing b s with
  | zero => exact terminalReserve 16 b s (by simpa using hs)
  | succ d ih =>
    let t : Fin 16 := ⟨16-(d+1),by omega⟩
    have now : t.val = 16-(d+1) := rfl
    have next : t.val+1 = 16-d := by omega
    have ht : 16-(d+1)<16 := by omega
    have dep := depends (⟨t.val,by omega⟩ : Fin 17) b (chosen t) (le_of_eq ((ranks t _).mpr rfl).symm)
    have nonconst (v : Bool) (ok : (flexible (chosen t) && v) = v) :
        ∃ x y, pinned t.val b (Function.update x (chosen t) v) ≠ pinned t.val b (Function.update y (chosen t) v) := by
      have d34 := depends (⟨t.val+1,by omega⟩ : Fin 17) (Function.update b (chosen t) v) 0 (by
        change t.val+1 ≤ rank 0
        have live : rank 0 = 16 := by decide
        omega)
      obtain ⟨x,hx⟩ := d34
      have e := congrFun (pinNext t b v ok)
      exact ⟨_,_,(e _).trans_ne (hx.trans_eq (e _).symm)⟩
    by_cases hf : flexible (chosen t) = true
    · obtain ⟨v,z,hz,hsmall⟩ := gate_elim_at 25 (pinned t.val b) (chosen t) s dep
        (fun v => nonconst v (by simp [hf])) hs
      rw [pinNext t b v (by simp [hf]), next] at hsmall
      have ll := ih (by omega) _ _ hsmall
      have w : extra (d+1) = extra d + 2 := by
        rw [extra, dite_eq_left ht]
        change extra d + (if flexible (chosen t) then 2 else 1) = extra d + 2
        simp [hf]
      omega
    · have sf := terminalReserve (⟨t.val,by omega⟩ : Fin 17) b s hs
      obtain ⟨z,rfl⟩ : ∃ z, s=z+1 := ⟨s-1,by omega⟩
      have hsmall := pin_fixed 25 (pinned t.val b) (chosen t) false z dep
        (nonconst false (by simp)) hs
      rw [pinNext t b false (by simp), next] at hsmall
      have ll := ih (by omega) _ _ hsmall
      have hff : flexible (chosen t) = false := Bool.eq_false_iff.mpr hf
      have w : extra (d+1) = extra d + 1 := by
        rw [extra, dite_eq_left ht]
        change extra d + (if flexible (chosen t) then 2 else 1) = extra d + 1
        simp [hff]
      omega

theorem lower (s : ℕ) (h : HasCircuitSize 26 target s) : 31 ≤ s := by
  let b : V → Bool := fun _ => false
  have e : pinned 0 b = target := by
    funext x
    have id : overlay 0 b x = x := by funext i; simp [overlay]
    exact congrArg target id
  have h' := inductiveBound 16 (by decide) b s (by simpa [e] using h)
  have he : extra 16 = 22 := by decide
  omega

end Plane1988.Elimination
#print axioms Plane1988.Elimination.lower
