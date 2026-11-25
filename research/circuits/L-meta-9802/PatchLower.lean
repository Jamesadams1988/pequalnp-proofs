import IncidenceTransfer
import PEqualNP.MetaComplexity.Helpers.Support

/-! A black-box repair sees the old output and the twelve vertices of its
two missing stars. Even on boundary patterns realizable by the full graph,
any fan-in-two repair needs at least twelve gates. -/
namespace Row9802.Transfer.Patch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Row4201.PGSequence (accepts)
open Row9802.Upper114 (edges)

private def oldBit (x : Fin 42 → Bool) : Bool := edges.any fun e =>
  x (emb (Fin.ofNat 40 e.1)) && x (emb (Fin.ofNat 40 e.2))

private theorem bounds : ∀ e ∈ edges, e.1 < 40 ∧ e.2 < 40 := by decide +kernel

private theorem oldBit_spec (x : Fin 42 → Bool) : oldBit x = true ↔ small (x ∘ emb) := by
  rw [oldBit,List.any_eq_true]
  constructor
  · rintro ⟨⟨i,j⟩,h,hw⟩
    have b := bounds (i,j) h
    have bi : i < 40 := b.1
    have bj : j < 40 := b.2
    refine ⟨Fin.ofNat 40 i,Fin.ofNat 40 j,?_,(Bool.and_eq_true_iff.mp hw).1,
      (Bool.and_eq_true_iff.mp hw).2⟩
    change (i % 40,j % 40) ∈ edges
    rwa [Nat.mod_eq_of_lt bi,Nat.mod_eq_of_lt bj]
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨(i.val,j.val),h,?_⟩
    simpa using (Bool.and_eq_true_iff.mpr ⟨hi,hj⟩)

private def testStar (x : Fin 42 → Bool) (c f : Fin 42) (t : List (Fin 42)) :=
  x c && (f::t).any x

private def fullBit (x : Fin 42 → Bool) :=
  oldBit x || (testStar x 0 21 pointTail || testStar x 22 1 lineTail)

private theorem fullBit_spec (x : Fin 42 → Bool) : fullBit x = true ↔ accepts x := by
  rw [decomposition]
  simp [fullBit,testStar, Bool.or_eq_true, oldBit_spec,star]

/-- Slots 1 and 2 are the missing point and line. Slots 3–7 are the lines
through the missing point, and slots 8–12 are the points on the missing line. -/
def boundary : Fin 12 → Fin 42 := ![0,22,21,26,28,38,41,1,2,5,15,17]

def visible (x : Fin 42 → Bool) : Fin 13 → Bool :=
  Fin.cases (oldBit x) (fun j => x (boundary j))

private def seed (k : Fin 13) : List (Fin 42) :=
  if k=0 then [] else if k=1 then [21] else if k=2 then [1] else if k.val ≤ 7 then [0] else [22]

private def next (k : Fin 13) : List (Fin 42) :=
  if h : k.val=0 then [3,24] else boundary ⟨k.val-1,by omega⟩ :: seed k

private def bits (S : List (Fin 42)) (v : Fin 42) := decide (v ∈ S)

/-- Both settings in each of the thirteen sensitivity tests are genuine
42-input assignments. The result still holds when the black box need
only be correct on the attainable subset of its thirteen-bit domain. -/
private theorem tests : ∀ k : Fin 13,
    (∀ j, visible (bits (next k)) j =
      Function.update (visible (bits (seed k))) k (!(visible (bits (seed k)) k)) j) ∧
    fullBit (bits (seed k)) = false ∧ fullBit (bits (next k)) = true := by
  decide +kernel

theorem blackBoxLower (D : Circuit) (legal : FanInTwo D)
    (computes : ∀ x, D.eval (List.ofFn (visible x)) = true ↔ accepts x) :
    12 ≤ D.size := by
  let f := fun y : Fin 13 → Bool => D.eval (List.ofFn y)
  have depends (k : Fin 13) : ∃ y : Fin 13 → Bool, f (Function.update y k (!(y k))) ≠ f y := by
    obtain ⟨sw,lo,hi⟩ := tests k
    refine ⟨visible (bits (seed k)),?_⟩
    rw [←funext sw]
    intro same
    have accept := (computes _).mpr ((fullBit_spec _).mp hi)
    change f (visible (bits (next k))) = true at accept
    have := (fullBit_spec _).mpr ((computes _).mp (same ▸ accept))
    simp_all
  have bound := Helpers.dep_lower 13 f depends D.size ⟨D,legal,le_rfl,fun _ => rfl⟩
  omega

end Row9802.Transfer.Patch
#print axioms Row9802.Transfer.Patch.blackBoxLower
