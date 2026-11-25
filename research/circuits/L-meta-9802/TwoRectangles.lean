import CoverStability

/-! A rank-two rectangular upper approximation of a matching excludes at most one
unordered nontrivial partition of its edges. In the order-four deletion graph a
nine-edge induced matching consequently forces at least 255 such approximations.
-/
namespace Row9802.TwoRectangles
open Row9802.CoverStability
abbrev I := Fin 9
abbrev Cut := {S : Finset I // 8 ∉ S ∧ S.Nonempty}

structure Rect where
  left : Finset I
  right : Finset I

def diag (r : Rect) (i : I) := i ∈ r.left ∧ i ∈ r.right
def hit (r : Rect) (X Y : Finset I) := (∃ i ∈ X, i ∈ r.left) ∧ (∃ j ∈ Y, j ∈ r.right)

private theorem monoSide (r : Rect) (S : Cut) (hn : ¬hit r S.val S.valᶜ) {i j : I}
    (hi : diag r i) (hj : diag r j) : i ∈ S.val ↔ j ∈ S.val := by
  constructor
  · intro inside; by_contra outside
    exact hn ⟨⟨i,inside,hi.1⟩,j,Finset.mem_compl.mpr outside,hj.2⟩
  · intro inside; by_contra outside
    exact hn ⟨⟨j,inside,hj.1⟩,i,Finset.mem_compl.mpr outside,hi.2⟩

private theorem canonical (a b : Rect) (S : Cut) (cover : ∀ i, diag a i ∨ diag b i)
    (anchor : diag a 8) (ha : ¬hit a S.val S.valᶜ) (hb : ¬hit b S.val S.valᶜ) :
    ∀ i, i ∈ S.val ↔ diag b i := by
  have forward (i : I) (hi : i ∈ S.val) : diag b i :=
    (cover i).resolve_left (fun h => S.property.1 ((monoSide a S ha h anchor).mp hi))
  intro i
  refine ⟨forward i, ?_⟩
  obtain ⟨j,hj⟩ := S.property.2
  exact fun good => (monoSide b S hb (forward j hj) good).mp hj

private theorem uniqueCut (a b : Rect) (cover : ∀ i, diag a i ∨ diag b i) {S T : Cut}
    (hs : ¬(hit a S.val S.valᶜ ∨ hit b S.val S.valᶜ))
    (ht : ¬(hit a T.val T.valᶜ ∨ hit b T.val T.valᶜ)) : S=T := by
  apply Subtype.ext; apply Finset.ext; intro i
  rcases cover 8 with ha | hb
  · exact (canonical a b S cover ha (fun h => hs (.inl h)) (fun h => hs (.inr h)) i).trans
      (canonical a b T cover ha (fun h => ht (.inl h)) (fun h => ht (.inr h)) i).symm
  · have swap (k) := (cover k).symm
    exact (canonical b a S swap hb (fun h => hs (.inr h)) (fun h => hs (.inl h)) i).trans
      (canonical b a T swap hb (fun h => ht (.inr h)) (fun h => ht (.inl h)) i).symm

 def points : I → ℕ := ![4,3,7,6,15,9,0,1,2]
 def lines : I → ℕ := ![24,30,32,33,35,36,37,38,39]

theorem induced : ∀ i j, (points i,lines j) ∈ edges ↔ i=j := by decide +kernel

def graph (X Y : Finset I) := ∃ i ∈ X, ∃ j ∈ Y, (points i,lines j) ∈ edges

set_option maxRecDepth 12000 in
theorem cutCard : Fintype.card Cut = 255 := by decide +kernel

/-- Any AND of two-rectangle union factors agreeing with the literal graph even just
on the selected nine points and lines requires at least 255 factors. -/
theorem widthTwoFloor {m : ℕ} (a b : Fin m → Rect)
    (correct : ∀ X Y : Finset I, graph X Y ↔ ∀ j, hit (a j) X Y ∨ hit (b j) X Y) : 255 ≤ m := by
  classical
  have cv (j : Fin m) (i : I) : diag (a j) i ∨ diag (b j) i := by
    have good : graph {i} {i} := ⟨i,by simp,i,by simp,(induced i i).mpr rfl⟩
    simpa [hit,diag] using (correct _ _).mp good j
  have misses (S : Cut) : ∃ j, ¬(hit (a j) S.val S.valᶜ ∨ hit (b j) S.val S.valᶜ) := by
    by_contra! h
    obtain ⟨i,hi,k,hk,edge⟩ := (correct _ _).mpr h
    obtain rfl := (induced i k).mp edge
    exact (Finset.mem_compl.mp hk) hi
  choose tag bad using misses
  have inj : Function.Injective tag := by
    intro S T eq
    exact uniqueCut (a (tag T)) (b (tag T)) (cv (tag T)) (eq ▸ bad S) (bad T)
  simpa [cutCard] using Fintype.card_le_of_injective tag inj
end Row9802.TwoRectangles
#print axioms Row9802.TwoRectangles.widthTwoFloor
