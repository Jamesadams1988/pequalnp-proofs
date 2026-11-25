import SignedChildren
import Rectangle

namespace Row12096Signed.SemanticCuts
open Row12096Signed Row12096Rectangle

def leavesOnly : List W → Finset W
  | [w] => {w, ~~~w}
  | _ => ∅

/-- Signed read-once values on a small side. The depth bound bounds tree height. -/
def smallValues : ℕ → List W → Finset W
  | 0, ws => leavesOnly ws
  | n+1, ws => leavesOnly ws ∪ (partitions ws).toFinset.biUnion (fun (a,b) =>
      if a.isEmpty || b.isEmpty then ∅ else
      (smallValues n a).biUnion fun x => (smallValues n b).biUnion fun y =>
        {x &&& y, ~~~(x &&& y)})

theorem realizesPerm {a b : List W} {u : W} (h : realizes a u) (p : a.Perm b) : realizes b u := by
  obtain ⟨t, ht, pol⟩ := h
  exact ⟨t, ht.trans p, pol⟩

private theorem leavesOnlyComplete {ws : List W} {u : W} (h : realizes ws u) (len : ws.length ≤ 1) :
    u ∈ leavesOnly ws := by
  obtain ⟨t, hp, pol⟩ := h
  cases t with
  | leaf x =>
    have he : ws = [x] := by simpa [Tree.leaves] using hp.symm
    rw [he]
    simpa [leavesOnly, Tree.value] using pol
  | gate o a b =>
    have he := hp.length_eq
    simp only [Tree.leaves, List.length_append] at he
    have al := List.length_pos_iff.mpr (leavesNonempty a)
    have bl := List.length_pos_iff.mpr (leavesNonempty b)
    omega

theorem smallValuesComplete (n : ℕ) {ws : List W} {u : W} (h : realizes ws u) (len : ws.length ≤ n+1) :
    u ∈ smallValues n ws := by
  induction n generalizing ws u with
  | zero => exact leavesOnlyComplete h len
  | succ n ih =>
    by_cases one : ws.length ≤ 1
    · exact Finset.mem_union_left _ (leavesOnlyComplete h one)
    obtain ⟨a,b,ha,hb,perm,l,r,hl,hr,pol⟩ := realizesSplit h (by omega)
    obtain ⟨⟨aa,bb⟩, hm, pa, pb⟩ := partitions_complete perm
    have partLen := perm.length_eq
    simp only [List.length_append] at partLen
    have ap := List.length_pos_iff.mpr ha
    have bp := List.length_pos_iff.mpr hb
    have aLen := pa.length_eq
    have bLen := pb.length_eq
    have vl := ih (realizesPerm hl pa.symm) (by omega)
    have vr := ih (realizesPerm hr pb.symm) (by omega)
    have notA : aa.isEmpty = false := by cases aa <;> simp_all
    have notB : bb.isEmpty = false := by cases bb <;> simp_all
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(aa,bb), List.mem_toFinset.mpr hm, ?_⟩
    simp only [notA, notB, Bool.false_or, Bool.false_eq_true, ite_false, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton]
    exact ⟨l, vl, r, vr, pol⟩

#print axioms smallValuesComplete
end Row12096Signed.SemanticCuts
