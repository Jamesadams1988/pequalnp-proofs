import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace Row9769.Elimination
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.PermInputs

abbrev V := Fin 42
def edges : List (V × V) := [(0,26), (0,28), (0,38), (0,41), (1,21), (1,22), (1,27), (1,29), (1,39), (2,22), (2,23), (2,28), (2,30), (2,40), (3,23), (3,24), (3,29), (3,31), (3,41), (4,21), (4,24), (4,25), (4,30), (4,32), (5,22), (5,25), (5,26), (5,31), (5,33), (6,23), (6,26), (6,27), (6,32), (6,34), (7,24), (7,27), (7,28), (7,33), (7,35), (8,25), (8,28), (8,29), (8,34), (8,36), (9,26), (9,29), (9,30), (9,35), (9,37), (10,27), (10,30), (10,31), (10,36), (10,38), (11,28), (11,31), (11,32), (11,37), (11,39), (12,29), (12,32), (12,33), (12,38), (12,40), (13,30), (13,33), (13,34), (13,39), (13,41), (14,21), (14,31), (14,34), (14,35), (14,40), (15,22), (15,32), (15,35), (15,36), (15,41), (16,21), (16,23), (16,33), (16,36), (16,37), (17,22), (17,24), (17,34), (17,37), (17,38), (18,23), (18,25), (18,35), (18,38), (18,39), (19,24), (19,26), (19,36), (19,39), (19,40), (20,25), (20,27), (20,37), (20,40), (20,41)]
def target (x : V → Bool) := edges.any fun e => x e.1 && x e.2
def rank : V → ℕ := ![4,7,6,5,8,8,8,3,8,2,8,1,0,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8]
def chosen : Fin 8 → V := ![12,11,9,7,0,3,2,1]
def witness : Fin 9 → V → V := ![
  ![26,21,22,23,21,22,23,24,25,26,27,28,29,30,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,9,0,1,2,0],
  ![26,21,22,23,21,22,23,24,25,26,27,28,0,30,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,9,0,1,2,0],
  ![26,21,22,23,21,22,23,24,25,26,27,0,0,30,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,9,0,1,2,0],
  ![41,21,22,23,21,22,23,24,25,0,27,0,0,34,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,16,0,1,2,0],
  ![41,21,22,23,21,22,23,0,25,0,36,0,0,34,21,22,21,22,23,36,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,14,8,16,0,1,2,0],
  ![0,21,22,23,21,22,23,0,25,0,36,0,0,34,21,22,21,22,23,36,25,1,1,2,3,4,5,1,2,1,2,3,4,5,6,14,8,16,10,1,2,3],
  ![0,21,22,0,21,22,34,0,25,0,36,0,0,34,21,22,21,22,25,36,25,1,1,2,4,4,5,1,2,1,2,5,4,5,6,14,8,16,10,1,2,13],
  ![0,21,0,0,21,25,34,0,25,0,36,0,0,34,21,36,21,34,25,36,25,1,1,6,4,4,5,1,8,1,4,5,4,5,6,14,8,16,10,1,14,13],
  ![0,0,0,0,25,25,34,0,25,0,36,0,0,34,34,36,36,34,25,36,25,4,5,6,4,4,5,6,8,8,4,5,4,5,6,14,8,16,10,13,14,13]]

def overlay (t : ℕ) (b x : V → Bool) (i : V) : Bool := if rank i < t then b i else x i

def pinned (t : ℕ) (b x : V → Bool) := target (overlay t b x)

def low (t : Fin 9) (i j : V) : Bool := decide (j = witness t i)

theorem tests : ∀ t : Fin 9, ∀ i : V, t.val ≤ rank i →
    low t i i = false ∧ target (overlay t.val (fun _ => true) (low t i)) = false ∧
    target (overlay t.val (fun _ => false) (Function.update (low t i) i true)) = true := by decide +kernel

theorem ranks : ∀ t : Fin 8, ∀ i : V, rank i = t.val ↔ i = chosen t := by decide +kernel

theorem monotoneTarget {x y : V → Bool} (h : ∀ i, x i = true → y i = true) : target x = true → target y = true := by
  intro hx
  obtain ⟨e,he,hb⟩ := List.any_eq_true.mp hx
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hb
  exact List.any_eq_true.mpr ⟨e,he,Bool.and_eq_true_iff.mpr ⟨h _ a,h _ b⟩⟩

theorem depends (t : Fin 9) (b : V → Bool) (i : V) (live : t.val ≤ rank i) :
    ∃ x, pinned t.val b (Function.update x i (!x i)) ≠ pinned t.val b x := by
  refine ⟨low t i, ?_⟩
  obtain ⟨atI,lo,hi⟩ := tests t i live
  have hif : pinned t.val b (Function.update (low t i) i true) = true :=
    monotoneTarget (fun j => by unfold overlay; split <;> simp) hi
  have lof : pinned t.val b (low t i) ≠ true := fun l => by
    have : target (overlay t.val (fun _ => true) (low t i)) = true := monotoneTarget (x := overlay t.val b (low t i)) (fun j => by unfold overlay; split <;> simp) l
    exact Bool.noConfusion (this.symm.trans lo)
  rw [atI]; simp only [Bool.not_false,hif]
  exact Ne.symm lof

theorem pinNext (t : Fin 8) (b : V → Bool) (v : Bool) :
    (fun x => pinned t.val b (Function.update x (chosen t) v)) = pinned (t.val+1) (Function.update b (chosen t) v) := by
  funext x
  unfold pinned
  congr 1
  funext i
  have eq := ranks t i
  by_cases hi : i = chosen t
  · subst i
    have h := eq.mpr rfl
    simp [overlay,h]
  · have h := not_iff_not.mpr eq |>.mpr hi
    have iff : rank i < t.val+1 ↔ rank i < t.val := by omega
    simp [overlay,iff,Function.update_of_ne hi]

theorem liveCard : (Finset.univ.filter fun i : V => 8 ≤ rank i).card = 34 := by decide +kernel

theorem inductionBound (d : ℕ) (hd : d ≤ 8) (b : V → Bool) (s : ℕ)
    (hs : HasCircuitSize 42 (pinned (8-d) b) s) : 33 + 2*d ≤ s := by
  induction d generalizing b s with
  | zero =>
    have bound := dep_lower_set 42 (pinned 8 b) (Finset.univ.filter fun i : V => 8 ≤ rank i)
      (fun i hi => depends 8 b i (Finset.mem_filter.mp hi).2) s (by simpa using hs)
    rw [liveCard] at bound
    omega
  | succ d ih =>
    let t : Fin 8 := ⟨8-(d+1),by omega⟩
    have now : t.val = 8-(d+1) := rfl
    have next : t.val+1 = 8-d := by omega
    have dep := depends (⟨t.val,by omega⟩ : Fin 9) b (chosen t) (le_of_eq ((ranks t _).mpr rfl).symm)
    have nonconst (v : Bool) : ∃ x y, pinned t.val b (Function.update x (chosen t) v) ≠ pinned t.val b (Function.update y (chosen t) v) := by
      have d34 := depends (⟨t.val+1,by omega⟩ : Fin 9) (Function.update b (chosen t) v) 41 (by
        change t.val+1 ≤ rank 41
        have forty : rank 41 = 8 := by decide
        omega)
      obtain ⟨x,hx⟩ := d34
      have e := congrFun (pinNext t b v)
      exact ⟨_,_,(e _).trans_ne (hx.trans_eq (e _).symm)⟩
    obtain ⟨v,z,hz,hsmall⟩ := gate_elim_at 41 (pinned t.val b) (chosen t) s dep nonconst hs
    rw [pinNext, next] at hsmall
    have lower := ih (by omega) _ _ hsmall
    omega

theorem lower (s : ℕ) (h : HasCircuitSize 42 target s) : 49 ≤ s := by
  let b : V → Bool := fun _ => false
  have eq : pinned 0 b = target := by
    funext x
    have id : overlay 0 b x = x := by funext i; simp [overlay]
    exact congrArg target id
  exact inductionBound 8 (by decide) b s (by simpa [eq] using h)
end Row9769.Elimination
#print axioms Row9769.Elimination.lower

namespace Row9769.Elimination
open PEqualNP.MetaComplexity

/-- The desk edge predicate verbatim. -/
def literal := (fun x : Fin 42 → Bool => (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41))

theorem literal_lower (s : ℕ) (h : HasCircuitSize 42 literal s) : 49 ≤ s := by
  have eq : literal = target := by
    funext x
    simp [literal,target,edges,List.any_cons,Bool.or_assoc]
  exact lower s (eq ▸ h)

end Row9769.Elimination
#print axioms Row9769.Elimination.literal_lower
