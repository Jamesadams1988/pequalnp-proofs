import HexSignature
import ZeroSensitivity

namespace HexNormalize
open Row4201.HexFour PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Code : ℕ → Type
 | start : Code 0
 | push {k} (c : Code k) (l r : BitVec (6+k)) : Code (k+1)

def wires {k} (c : Code k) (x : BitVec 6) : BitVec (6+k) :=
  match c with
  | .start => x
  | .push u l r => step (wires u x) l r

def Has {k} (c : Code k) (f : BitVec 6 → Bool) : Prop :=
  ∃ mask, ∀ x : BitVec 6, x ≠ 63 → meet (wires c x) mask = f x

private theorem bitSpec {n} (w s : BitVec n) : meet w s = true ↔
    ∀ i, i < n → s.getLsbD i = true → w.getLsbD i = true := by
  simp only [meet,beq_iff_eq,BitVec.eq_of_getLsbD_eq_iff,BitVec.getLsbD_and,
    BitVec.getLsbD_not]
  constructor
  · intro h i hi hs
    have a := h i hi
    simpa [hs,hi] using a
  · intro h i hi
    by_cases hs : s.getLsbD i = true <;> simp_all

private theorem liftBit {k : ℕ} (_hk : k ≤ 4) (w s l r : BitVec (6+k)) :
    meet (step w l r) (BitVec.cons false s) = meet w s := by
  apply Bool.eq_iff_iff.mpr
  rw [bitSpec,bitSpec]
  simp only [step,BitVec.getLsbD_cons]
  constructor
  · intro h i hi hs
    have hn : i ≠ 6+k := by omega
    simpa [hn] using h i (by omega) (by simpa [hn] using hs)
  · intro h i hi hs
    by_cases he : i = 6+k
    · simp [he] at hs
    · simpa [he] using h i (by omega) (by simpa [he] using hs)

private theorem lastBit {k : ℕ} (_hk : k ≤ 4) (w l r : BitVec (6+k)) :
    meet (step w l r) (BitVec.cons true 0) = (meet w l || meet w r) := by
  apply Bool.eq_iff_iff.mpr
  rw [bitSpec]
  simp only [step,BitVec.getLsbD_cons]
  constructor
  · intro h
    simpa using h (6+k) (by omega) (by simp)
  · intro h i _ hi
    split_ifs at hi ⊢ <;> simp_all

private theorem combineBit {k : ℕ} (_hk : k ≤ 4) (w l r : BitVec (6+k)) :
    meet w (l ||| r) = (meet w l && meet w r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,bitSpec,BitVec.getLsbD_or,Bool.or_eq_true]
  grind

private theorem trueBit {k : ℕ} (_hk : k ≤ 4) (w : BitVec (6+k)) : meet w 0 = true := by
  simp [bitSpec]

theorem lift {k} (hk : k ≤ 4) (c : Code k) (l r : BitVec (6+k)) {f} (hf : Has c f) :
    Has (c.push l r) f := by
  obtain ⟨s,hs⟩ := hf
  exact ⟨BitVec.cons false s,fun x hx => (liftBit hk _ _ _ _).trans (hs x hx)⟩

theorem top {k} (hk : k ≤ 4) (c : Code k) : Has c (fun _ => true) :=
  ⟨0,fun _ _ => trueBit hk _⟩

theorem bot {k} (hk : k ≤ 4) (c : Code k) : Has c (fun _ => false) := by
  induction c with
  | start =>
    refine ⟨63, fun x hx => ?_⟩
    change meet x 63 = false
    revert x
    decide +kernel
  | push u l r ih => exact lift (by omega) u l r (ih (by omega))

theorem andHas {k} (hk : k ≤ 4) {c : Code k} {f g} (hf : Has c f) (hg : Has c g) :
    Has c (fun x => f x && g x) := by
  obtain ⟨l,hl⟩ := hf
  obtain ⟨r,hr⟩ := hg
  exact ⟨l ||| r,fun x hx => by rw [combineBit hk,hl x hx,hr x hx]⟩

theorem orPush {k} (hk : k ≤ 4) (c : Code k) {f g} (hf : Has c f) (hg : Has c g) :
    ∃ l r, Has (c.push l r) (fun x => f x || g x) := by
  obtain ⟨l,hl⟩ := hf
  obtain ⟨r,hr⟩ := hg
  exact ⟨l,r,BitVec.cons true 0,fun x hx => by change meet (step _ _ _) _ = _; rw [lastBit hk,hl x hx,hr x hx]⟩

theorem pad {k} (c : Code k) (t : ℕ) (ht : k+t ≤ 4) :
    ∃ u : Code (k+t), ∀ f, Has c f → Has u f := by
  induction t with
  | zero => exact ⟨c,fun _ h => h⟩
  | succ t ih =>
    obtain ⟨u,hu⟩ := ih (by omega)
    exact ⟨u.push 0 0, fun f h => lift (by omega) u 0 0 (hu f h)⟩

def gate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => w.getD i false))
def addWire (w : List Bool) (g : Gate) := w ++ [gate w g]
def Rep {k} (c : Code k) (w : BitVec 6 → List Bool) := ∀ i, Has c (fun x => (w x).getD i false)

private theorem appended (a : List Bool) (b : Bool) (i : ℕ) :
    (a ++ [b]).getD i false = if i=a.length then b else a.getD i false := by
  induction a generalizing i with
  | nil => cases i <;> simp
  | cons v vs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.getD_cons_succ] using ih i

theorem updated {k} (c : Code k) (w : BitVec 6 → List Bool)
    (len : ∀ x, (w x).length = (w 0).length) (prev : Rep c w) (g : Gate)
    (ng : Has c (fun x => gate (w x) g)) : Rep c (fun x => addWire (w x) g) := by
  intro i
  by_cases hi : i=(w 0).length
  · simpa only [addWire,appended,len,ite_eq_left hi] using ng
  · simpa only [addWire,appended,len,ite_eq_right hi] using prev i

theorem allHas {k} (hk : k ≤ 4) (c : Code k) (w : BitVec 6 → List Bool)
    (hw : Rep c w) (l : List ℕ) : Has c (fun x => (l.map (fun i => (w x).getD i false)).all id) := by
  induction l with
  | nil => simpa using top hk c
  | cons i l ih => simpa using andHas hk (hw i) ih

end HexNormalize
