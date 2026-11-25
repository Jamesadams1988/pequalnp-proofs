import SignedFrontier

namespace Row12096Compact
open Row12096Signed

/-- Keep only the states whose paired truth-table columns still separate every row. -/
def offer (enabled : Bool) (s : State) : List State := if enabled then [s] else []

def afterGate (e : Nat) (a b z : W) (r : List W) : List State :=
  let cover := sep z ||| cuts r
  offer (cover == -1) (e, z :: r) ++
  offer (e != 0 && (cover ||| sep a == -1)) (e-1, z :: a :: r) ++
  offer (e != 0 && (cover ||| sep b == -1)) (e-1, z :: b :: r) ++
  offer (decide (e ≥ 2) && (cover ||| sep a ||| sep b == -1)) (e-2, z :: a :: b :: r)

def children (s : State) : List State := (pairs s.2).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z => afterGate s.1 a b z r

def doneAt (s : State) := s.2 == [goal] || s.2 == [~~~goal]

private theorem anyFlat {α β : Type} (xs : List α) (f : α → List β) (p : β → Bool) :
    (xs.flatMap f).any p = xs.any (fun a => (f a).any p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem anyOffer (p : State → Bool) (b : Bool) (s : State) :
    (offer b s).any p = (b && p s) := by cases b <;> simp [offer]

theorem layer_eq (f : Nat → List W → Bool) (s : State) :
    nextLayer f s.1 s.2 = (doneAt s || (children s).any (fun p => f p.1 p.2)) := by
  unfold nextLayer doneAt children
  rw [anyFlat]
  congr 1
  apply congrArg (List.any (pairs s.2))
  funext ⟨a,b,r⟩
  unfold dispatch
  rw [anyFlat]
  apply congrArg (List.any (ops a b))
  funext z
  simp only [afterGate, List.any_append, anyOffer]
  generalize (sep z ||| cuts r == -1) = p
  generalize (s.1 != 0) = q
  generalize (sep z ||| cuts r ||| sep a == -1) = u
  generalize (sep z ||| cuts r ||| sep b == -1) = v
  cases q <;> simp [Bool.or_assoc, Bool.and_assoc]

def rejected (d : Nat) (ss : List State) := ss.all (fun q => !optimized d q.1 q.2)

theorem rejectChildren (d : Nat) (s : State) (miss : doneAt s = false)
    (h : rejected d (children s) = true) : optimized (d+1) s.1 s.2 = false := by
  change nextLayer (optimized d) s.1 s.2 = false
  rw [layer_eq, miss, Bool.false_or]
  cases answer : (children s).any (fun p => optimized d p.1 p.2) with
  | false => rfl
  | true =>
    obtain ⟨p, hp, hit⟩ := List.any_eq_true.mp answer
    have no := List.all_eq_true.mp h p hp
    simp [hit] at no

theorem merge (d cut : Nat) (ss : List State)
    (left : rejected d (ss.take cut) = true) (right : rejected d (ss.drop cut) = true) :
    rejected d ss = true := by
  have both : rejected d (ss.take cut ++ ss.drop cut) = true := by
    simpa only [rejected, List.all_append, Bool.and_eq_true] using And.intro left right
  simpa using both

theorem mergeAt (d start width : Nat) (ss : List State)
    (part : rejected d ((ss.drop start).take width) = true)
    (rest : rejected d (ss.drop (start + width)) = true) :
    rejected d (ss.drop start) = true := by
  apply merge d width (ss.drop start) part
  simpa [List.drop_drop, Nat.add_comm] using rest

end Row12096Compact
#print axioms Row12096Compact.rejectChildren
#print axioms Row12096Compact.merge
