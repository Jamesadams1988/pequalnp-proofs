import PGSequence
import Upper114

/-! L-meta-9802 is the Singer plane with point 0 and line 22 removed. -/
namespace Row9802.Transfer
open Row4201.PGSequence
open Row9802.Upper114 (edges)

def smallEdge (i j : Fin 40) := (i.val,j.val) ∈ edges
instance (i j : Fin 40) : Decidable (smallEdge i j) := by unfold smallEdge; infer_instance
def small (x : Fin 40 → Bool) := ∃ i j, smallEdge i j ∧ x i = true ∧ x j = true

def emb (i : Fin 40) : Fin 42 := ⟨if i.val < 21 then i.val+1 else i.val+2,by split <;> omega⟩
def back (v : Fin 42) : Fin 40 := Fin.ofNat 40 (if v.val < 22 then v.val-1 else v.val-2)
def kept (v : Fin 42) : Bool := decide (v ≠ 0 ∧ v ≠ 22)

theorem retraction : ∀ i : Fin 40, back (emb i) = i := by decide +kernel
theorem embeddingKept : ∀ i : Fin 40, kept (emb i) = true := by decide +kernel
theorem reconstruct : ∀ v : Fin 42, kept v = true → emb (back v) = v := by decide +kernel

def pointTail : List (Fin 42) := [26,28,38,41]
def lineTail : List (Fin 42) := [2,5,15,17]

theorem edgeSplit : ∀ p l : Fin 42, incident p l ↔
    (kept p = true ∧ kept l = true ∧ smallEdge (back p) (back l)) ∨
    (p = 0 ∧ l ∈ 21 :: pointTail) ∨ (l = 22 ∧ p ∈ 1 :: lineTail) := by
  decide +kernel

def star {n} (x : Fin n → Bool) (c f : Fin n) (t : List (Fin n)) : Prop :=
  x c = true ∧ ∃ v ∈ f::t, x v = true

theorem decomposition (x : Fin 42 → Bool) :
    accepts x ↔ small (x ∘ emb) ∨ star x 0 21 pointTail ∨ star x 22 1 lineTail := by
  constructor
  · rintro ⟨p,l,h,hp,hl⟩
    rcases (edgeSplit p l).mp h with ⟨kp,kl,e⟩ | ⟨rfl,mem⟩ | ⟨rfl,mem⟩
    · exact Or.inl ⟨back p,back l,e,by simpa [Function.comp_def,reconstruct p kp] using hp,
        by simpa [Function.comp_def,reconstruct l kl] using hl⟩
    · exact Or.inr (Or.inl ⟨hp,l,mem,hl⟩)
    · exact Or.inr (Or.inr ⟨hl,p,mem,hp⟩)
  · rintro (⟨i,j,h,hi,hj⟩ | ⟨hp,l,mem,hl⟩ | ⟨hl,p,mem,hp⟩)
    · exact ⟨emb i,emb j,(edgeSplit _ _).mpr (Or.inl ⟨embeddingKept _,embeddingKept _,
        by simpa only [retraction] using h⟩),hi,hj⟩
    · exact ⟨0,l,(edgeSplit _ _).mpr (Or.inr (Or.inl ⟨rfl,mem⟩)),hp,hl⟩
    · exact ⟨p,22,(edgeSplit _ _).mpr (Or.inr (Or.inr ⟨rfl,mem⟩)),hp,hl⟩

theorem onKept (x : Fin 40 → Bool) :
    accepts (fun v => (x ∘ back) v && kept v) ↔ small x := by
  rw [decomposition]
  have r : (fun v => (x ∘ back) v && kept v) ∘ emb = x := by
    funext i
    simp [Function.comp_def,retraction,embeddingKept]
  rw [r]
  have p : kept 0 = false := by decide
  have l : kept 22 = false := by decide
  simp only [star,p,l,Bool.and_false,Bool.false_eq_true,false_and,or_false]
end Row9802.Transfer
#print axioms Row9802.Transfer.decomposition
#print axioms Row9802.Transfer.onKept
