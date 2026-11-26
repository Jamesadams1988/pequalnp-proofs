import PEqualNP.MetaComplexity.Helpers.PermInputs

/-! Gate elimination specializes James Adams’s L-meta-9769 Terminal51 certificate to this 51-edge graph. -/
namespace Plane9742.Elimination
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs
abbrev V := Fin 26
def edges : List (V × V) := [(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
def target (x : V → Bool) := edges.any fun e => x e.1 && x e.2

def rank : V → ℕ := ![5, 10, 4, 18, 18, 12, 18, 1, 8, 16, 15, 6, 18, 11, 2, 0, 18, 3, 18, 18, 7, 9, 17, 18, 14, 13]
def chosen : Fin 18 → V := ![15, 7, 14, 17, 2, 0, 11, 20, 8, 21, 1, 13, 5, 25, 24, 10, 9, 22]
def flexible (i : V) : Bool := decide (i ∈ ({15,7,14,0,8,13,22} : Finset V))
def witness : Fin 19 → V → V := ![
  ![17, 13, 14, 13, 14, 15, 16, 17, 18, 13, 14, 15, 16, 1, 1, 2, 3, 0, 1, 2, 3, 4, 5, 0, 1, 0],
  ![17, 13, 14, 13, 14, 17, 16, 17, 18, 13, 14, 21, 16, 1, 1, 0, 4, 0, 1, 6, 7, 4, 9, 0, 1, 0],
  ![23, 13, 14, 13, 14, 18, 16, 0, 18, 13, 14, 21, 16, 1, 1, 0, 4, 0, 1, 6, 8, 4, 9, 0, 1, 0],
  ![23, 13, 25, 13, 16, 18, 16, 0, 18, 13, 22, 21, 16, 9, 0, 0, 6, 0, 6, 6, 8, 8, 9, 0, 12, 0],
  ![23, 13, 25, 13, 16, 18, 16, 0, 18, 13, 22, 21, 16, 9, 0, 0, 6, 0, 6, 6, 8, 8, 9, 0, 12, 0],
  ![23, 13, 0, 13, 16, 18, 16, 0, 18, 13, 22, 21, 16, 9, 0, 0, 6, 0, 6, 6, 8, 8, 9, 0, 12, 0],
  ![0, 13, 0, 13, 16, 18, 16, 0, 18, 13, 22, 21, 16, 9, 0, 0, 6, 0, 6, 6, 8, 8, 9, 6, 12, 8],
  ![0, 13, 0, 13, 16, 18, 16, 0, 18, 13, 22, 0, 16, 9, 0, 0, 6, 0, 6, 6, 8, 8, 9, 6, 12, 8],
  ![0, 13, 0, 13, 16, 18, 16, 0, 18, 13, 22, 0, 16, 9, 0, 0, 6, 0, 6, 6, 0, 8, 9, 6, 12, 8],
  ![0, 13, 0, 13, 16, 22, 16, 0, 0, 13, 22, 0, 16, 9, 0, 0, 6, 0, 6, 6, 0, 9, 9, 6, 12, 12],
  ![0, 13, 0, 13, 16, 22, 16, 0, 0, 13, 22, 0, 16, 9, 0, 0, 6, 0, 6, 6, 0, 0, 9, 6, 12, 12],
  ![0, 0, 0, 13, 16, 22, 16, 0, 0, 13, 22, 0, 16, 9, 0, 0, 6, 0, 6, 6, 0, 0, 9, 6, 12, 12],
  ![0, 0, 0, 16, 16, 22, 16, 0, 0, 22, 22, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 12, 12],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 22, 22, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 12, 12],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 22, 22, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 12, 0],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 22, 22, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 0, 0],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 22, 0, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 0, 0],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 12, 6, 0, 0],
  ![0, 0, 0, 16, 16, 0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 6, 0, 6, 6, 0, 0, 0, 6, 0, 0]]

def overlay (t : ℕ) (b x : V → Bool) (i : V) : Bool := if rank i < t then (flexible i && b i) else x i

def pinned (t : ℕ) (b x : V → Bool) := target (overlay t b x)

def low (t : Fin 19) (i j : V) : Bool := decide (j = witness t i)

set_option maxHeartbeats 8000000 in
theorem tests : ∀ t : Fin 19, ∀ i : V, t.val ≤ rank i →
    low t i i = false ∧ target (overlay t.val (fun _ => true) (low t i)) = false ∧
    target (overlay t.val (fun _ => false) (Function.update (low t i) i true)) = true := by decide +kernel

theorem ranks : ∀ t : Fin 18, ∀ i : V, rank i = t.val ↔ i = chosen t := by decide +kernel

theorem monotoneTarget {x y : V → Bool} (h : ∀ i, x i = true → y i = true) : target x = true → target y = true := by
  intro hx
  obtain ⟨e,he,hb⟩ := List.any_eq_true.mp hx
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hb
  exact List.any_eq_true.mpr ⟨e,he,Bool.and_eq_true_iff.mpr ⟨h _ a,h _ b⟩⟩

theorem depends (t : Fin 19) (b : V → Bool) (i : V) (live : t.val ≤ rank i) :
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

theorem pinNext (t : Fin 18) (b : V → Bool) (v : Bool) (ok : (flexible (chosen t) && v) = v) :
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

theorem liveCard : (Finset.univ.filter fun i : V => 18 ≤ rank i).card = 8 := by decide +kernel

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
  | d+1 => extra d + if h : 18-(d+1)<18 then
      (if flexible (chosen ⟨18-(d+1),h⟩) then 2 else 1) else 0

theorem terminalReserve (t : Fin 19) (b : V → Bool) (s : ℕ) (h : HasCircuitSize 26 (pinned t.val b) s) :
    7 ≤ s := by
  have h' := dep_lower_set 26 (pinned t.val b) (Finset.univ.filter fun i : V => 18 ≤ rank i)
    (fun i hi => depends t b i (by have := (Finset.mem_filter.mp hi).2; omega)) s h
  rw [liveCard] at h'
  omega

theorem inductiveBound (d : ℕ) (hd : d ≤ 18) (b : V → Bool) (s : ℕ)
    (hs : HasCircuitSize 26 (pinned (18-d) b) s) : 7 + extra d ≤ s := by
  induction d generalizing b s with
  | zero => exact terminalReserve 18 b s (by simpa using hs)
  | succ d ih =>
    let t : Fin 18 := ⟨18-(d+1),by omega⟩
    have now : t.val = 18-(d+1) := rfl
    have next : t.val+1 = 18-d := by omega
    have ht : 18-(d+1)<18 := by omega
    have dep := depends (⟨t.val,by omega⟩ : Fin 19) b (chosen t) (le_of_eq ((ranks t _).mpr rfl).symm)
    have nonconst (v : Bool) (ok : (flexible (chosen t) && v) = v) :
        ∃ x y, pinned t.val b (Function.update x (chosen t) v) ≠ pinned t.val b (Function.update y (chosen t) v) := by
      have d34 := depends (⟨t.val+1,by omega⟩ : Fin 19) (Function.update b (chosen t) v) 3 (by
        change t.val+1 ≤ rank 3
        have live : rank 3 = 18 := by decide
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
    · have sf := terminalReserve (⟨t.val,by omega⟩ : Fin 19) b s hs
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

theorem lower (s : ℕ) (h : HasCircuitSize 26 target s) : 32 ≤ s := by
  let b : V → Bool := fun _ => false
  have e : pinned 0 b = target := by
    funext x
    have id : overlay 0 b x = x := by funext i; simp [overlay]
    exact congrArg target id
  have h' := inductiveBound 18 (by decide) b s (by simpa [e] using h)
  have he : extra 18 = 25 := by decide
  omega

end Plane9742.Elimination
#print axioms Plane9742.Elimination.lower

namespace Plane9742.Elimination
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The desk's ordered edge pairs represented as natural numbers. -/
def edgePairs : List (ℕ × ℕ) := edges.map fun e => (e.1.val, e.2.val)

theorem hits (x : V → Bool) :
    target x = true ↔ ∃ u v : V, (u.val, v.val) ∈ edgePairs ∧ x u = true ∧ x v = true := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,hm,hb⟩ := List.any_eq_true.mp h
    exact ⟨u,v,List.mem_map_of_mem hm,Bool.and_eq_true_iff.mp hb⟩
  · rintro ⟨u,v,h,hu,hv⟩
    obtain ⟨⟨a,b⟩,hm,eq⟩ := List.mem_map.mp h
    have ha : a = u := Fin.ext (congrArg Prod.fst eq)
    have hb : b = v := Fin.ext (congrArg Prod.snd eq)
    subst a; subst b
    exact List.any_eq_true.mpr ⟨(u,v),hm,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩

theorem circuit_lower (C : Circuit) (hfan : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = true ↔
      ∃ u v : V, (u.val,v.val) ∈ edgePairs ∧ x u = true ∧ x v = true) : 32 ≤ C.size :=
  lower _ ⟨C,hfan,le_rfl,fun x => Bool.eq_iff_iff.mpr ((correct x).trans (hits x).symm)⟩

theorem literal_lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 31 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C,hm,hs,hc⟩
  have hf : FanInTwo C := by
    intro g hg
    obtain ⟨hop,hlen⟩ := hm g hg
    refine ⟨?_,hlen⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
    tauto
  have h := circuit_lower C hf hc
  omega
end Plane9742.Elimination
#print axioms Plane9742.Elimination.literal_lower
