import SignedFrontier
import Std.Tactic.BVDecide

/-! The signed build definitions and elementary simulation lemmas are from
L-meta-14930. The projection bound counts all current live wires that turn
into constants, even when several of them map to the same constant. -/
namespace Row12096Pin
open Row12096Signed
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

def isConst (v : W) := v = 0 ∨ v = ~~~0

instance (v : W) : Decidable (isConst v) := inferInstanceAs (Decidable (_ ∨ _))

def fixed (φ : W → W) (s : Finset W) := (s.filter fun w => isConst (φ w)).card

theorem fixed_insert_le (φ : W → W) (a : W) (s : Finset W) :
    fixed φ (insert a s) ≤ fixed φ s + (if isConst (φ a) then 1 else 0) := by
  by_cases h : isConst (φ a)
  · simpa [fixed,Finset.filter_insert,h] using Finset.card_insert_le a (s.filter fun w => isConst (φ w))
  · simp [fixed,Finset.filter_insert,h]

theorem fixed_insert_eq (φ : W → W) (a : W) (s : Finset W) (ha : a ∉ s) :
    fixed φ (insert a s) = fixed φ s + (if isConst (φ a) then 1 else 0) := by
  by_cases h : isConst (φ a) <;> simp [fixed,Finset.filter_insert,h,ha]

/-- A gate with a constant operand costs zero gates after projection. -/
theorem mem_ops_const {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hc : isConst x ∨ isConst y) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have zero : holds av (0 : W) := .inl rfl
  have one : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have nx := holds_not hx
  have ny := holds_not hy
  rcases hc with (rfl|rfl)|(rfl|rfl) <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first
    | assumption
    | (convert hx using 1 <;> bv_decide)
    | (convert hy using 1 <;> bv_decide)
    | (convert nx using 1 <;> bv_decide)
    | (convert ny using 1 <;> bv_decide)
    | (convert zero using 1 <;> bv_decide)
    | (convert one using 1 <;> bv_decide)

theorem op_const {x y z : W} (hx : isConst x) (hy : isConst y) (hz : z ∈ basicOps x y) :
    isConst z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> rcases hz with rfl|rfl|rfl|rfl <;> decide

/-- A successful live run that uses k binary gates and starts with c wires
which become constant under projection gives a signed build costing at most k-c. -/
theorem project_savings {φ : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → φ z ∈ basicOps (φ a) (φ b))
    {g : W} (ng : ¬isConst (φ g)) {k : ℕ} {s av : Finset W}
    (run : live basicOps g k s) (hav : ∀ u ∈ s, holds av (φ u)) :
    ∃ t, t + fixed φ s ≤ k ∧ SignedBuild t av (φ g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    subst s
    exact ⟨0,by simp [fixed,ng],sb_zero (hav _ (by simp))⟩
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,hn,r,eq,tail⟩
    · obtain ⟨t,ht,hr⟩ := ih skip hav
      exact ⟨t,by omega,hr⟩
    · have zr : z ∉ r := fun h => hn (eq ▸ by simp [h])
      have pre := fixed_insert_le φ a (insert b r)
      have pre' := fixed_insert_le φ b r
      have post := fixed_insert_eq φ z r zr
      have mapped := hm a b z hz
      have both := fun (h : isConst (φ a)) (h' : isConst (φ b)) => op_const h h' mapped
      have extendBank (av' : Finset W) (sub : av ⊆ av') (ok : holds av' (φ z)) :
          ∀ u ∈ insert z r, holds av' (φ u) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl|hr
        · exact ok
        · exact holds_mono sub (hav u (eq ▸ by simp [hr]))
      by_cases cheap : isConst (φ a) ∨ isConst (φ b)
      · have hpre : fixed φ s ≤ fixed φ (insert z r) + 1 := by
          rw [eq]
          by_cases ac : isConst (φ a)
          · by_cases bc : isConst (φ b)
            · have zc := both ac bc
              simp only [if_pos ac,if_pos bc,if_pos zc] at pre pre' post
              omega
            · simp [ac,bc] at pre pre'
              split_ifs at post <;> omega
          · have bc := cheap.resolve_left ac
            simp [ac,bc] at pre pre'
            split_ifs at post <;> omega
        have ok := mem_ops_const (hav a ha) (hav b hb) cheap mapped
        obtain ⟨t,ht,hr⟩ := ih tail (extendBank av (fun _ h => h) ok)
        exact ⟨t,by omega,hr⟩
      · have hpre : fixed φ s ≤ fixed φ (insert z r) := by
          rw [eq]
          obtain ⟨ac,bc⟩ := not_or.mp cheap
          simp [ac,bc] at pre pre'
          split_ifs at post <;> omega
        rcases mem_ops_reach (hav a ha) (hav b hb) mapped with ok|⟨a',ha',b',hb',ne,w,hw,ok⟩
        · obtain ⟨t,ht,hr⟩ := ih tail (extendBank av (fun _ h => h) ok)
          exact ⟨t,by omega,hr⟩
        · obtain ⟨t,ht,hr⟩ := ih tail (extendBank (insert w av) (Finset.subset_insert _ _) ok)
          exact ⟨t+1,by omega,sb_step ha' hb' ne hw hr⟩
def pinRows : Fin 32 → Fin 256 := ![121,0,9,27,1,128,137,155,31,50,62,3,156,178,190,192,69,87,99,4,193,215,227,229,111,5,6,230,239,243,246,248]
def laneAt (j : Fin 256) : Fin 256 := pinRows ⟨j.val % 32, Nat.mod_lt _ (by decide)⟩
def project  (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 256 => w[(laneAt j).val]))).cast List.length_ofFn

theorem project_bit (w : W) (j : ℕ) (hj : j < 256) :
    (project w)[j] = w[(laneAt ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [project, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem project_not  (w : W) : project (~~~w) = ~~~project w :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [project_bit, BitVec.getElem_not]

theorem project_ops  (a b z : W) (hz : z ∈ basicOps a b) :
    project z ∈ basicOps (project a) (project b) := by
  have hand (u v : W) : project (u &&& v) = (project u &&& project v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [project_bit, BitVec.getElem_and]
  have hor (u v : W) : project (u ||| v) = (project u ||| project v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [project_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl <;> simp [hand, hor, project_not]


def h13 := branch first 0 4 1 3
def h17 := branch h13 0 2 2 1

set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem twoFixed : fixed project h17.2.toFinset = 2 := by decide +kernel
theorem targetNonconstant : ¬ isConst (project goal) := by decide +kernel

theorem h17_pin {av : Finset W} (h : live basicOps goal 9 h17.2.toFinset)
    (a : ∀ w ∈ h17.2.toFinset, holds av (project w)) :
    ∃ t, t ≤ 7 ∧ SignedBuild t av (project goal) := by
  obtain ⟨t,ht,hb⟩ := project_savings project_ops targetNonconstant h a
  rw [twoFixed] at ht
  exact ⟨t,by omega,hb⟩

end Row12096Pin
#print axioms Row12096Pin.project_savings
#print axioms Row12096Pin.h17_pin
