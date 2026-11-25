import ChargeCount
import Separation
import ExtremalVerifier

/-! Restrict primary inputs to a fixed support. Each old gate retains its wire
index. Unneeded OR gates become AND copies; a copy of a permanently
out-of-range index produces false. No extra OR is introduced. -/
namespace Row4201.Restrict
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PG4Separation (prefixRead)
open Row4201.Charging (isOr)

variable {n : ℕ}
abbrev Row (n : ℕ) := Fin n → Bool

def mask (top x : Row n) (i : Fin n) := x i && top i

private def redirect (top : Row n) (bad i : ℕ) : ℕ :=
  if h : i < n then if top ⟨i,h⟩ then i else bad else i

private def copy (a : ℕ) : Gate := ⟨.and,[a]⟩

private def trim (g : Gate) (live : ℕ → Bool) (rename : ℕ → ℕ) (bad : ℕ) : Gate :=
  match g.op, g.inputs with
  | .or, [] => copy bad
  | .or, [a] => copy (rename a)
  | .or, [a,b] =>
    if live a && live b then ⟨.or,[rename a,rename b]⟩
    else if live a then copy (rename a) else copy (rename b)
  | op, xs => ⟨op,xs.map rename⟩

private def gateAt (C : Circuit) (top : Row n) (j : Fin C.gates.length) : Gate :=
  trim C.gates[j] (prefixRead C j top) (redirect top (n+C.gates.length)) (n+C.gates.length)

def toCore (C : Circuit) (top : Row n) : Circuit :=
  ⟨List.ofFn (gateAt C top), redirect top (n+C.gates.length) C.output⟩

private abbrev Legal (g : Gate) :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem trimLegal (g : Gate) (hg : Legal g) (l : ℕ → Bool) (r : ℕ → ℕ) (b : ℕ) :
    Legal (trim g l r b) := by
  rcases g with ⟨op,xs⟩
  obtain ⟨hop,len⟩ := hg
  change xs.length ≤ 2 at len
  rcases hop with h | h
  · change op = .and at h
    subst op
    simp [Legal,trim,len]
  · change op = .or at h
    subst op
    rcases xs with _ | ⟨a,_ | ⟨b',_ | ⟨_,_⟩⟩⟩
    · simp [Legal,trim,copy]
    · simp [Legal,trim,copy]
    · cases ha : l a <;> cases hb : l b' <;> simp [Legal,trim,copy,ha,hb]
    · simp at len

theorem toCore_mono (C : Circuit) (hc : Monotone2 C) (top : Row n) :
    Monotone2 (toCore C top) := by
  intro g hg
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
  exact trimLegal _ (hc _ (List.getElem_mem _)) _ _ _

private def val (g : Gate) (w : ℕ → Bool) := g.op.eval (g.inputs.map w)

private theorem trimVal (g : Gate) (hg : Legal g) (l r b)
    (old new : ℕ → Bool) (matchRead : ∀ i, new (r i) = old i)
    (zero : new b = false) (below : ∀ i, old i = true → l i = true) :
    val (trim g l r b) new = val g old := by
  rcases g with ⟨op,xs⟩
  obtain ⟨hop,len⟩ := hg
  change xs.length ≤ 2 at len
  rcases hop with h | h
  · change op = .and at h
    subst op
    simp [trim,val,List.map_map,Function.comp_def,matchRead]
  · change op = .or at h
    subst op
    rcases xs with _ | ⟨a,_ | ⟨c,_ | ⟨_,_⟩⟩⟩
    · simp [trim,copy,val,GateOp.eval,zero]
    · simp [trim,copy,val,GateOp.eval,matchRead]
    · have ha := below a
      have hb := below c
      cases e : l a <;> cases f : l c <;> cases u : old a <;> cases v : old c <;>
        simp_all [trim,copy,val,GateOp.eval]
    · simp at len

private theorem foldLen (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs,0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons, List.length_cons] at *
    rw [ih]
    simp
    omega

private theorem snocRead (ws : List Bool) (b : Bool) (i : ℕ) :
    (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
  induction ws generalizing i with
  | nil => cases i <;> simp
  | cons h t ih => cases i <;> simp_all

private theorem prefixSucc (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Row n) (i : ℕ) :
    prefixRead C (j+1) x i = if i = n+j then val C.gates[j] (prefixRead C j x)
                              else prefixRead C j x i := by
  unfold prefixRead Circuit.eval Circuit.wires
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,snocRead]
  have len := foldLen (C.gates.take j) (List.ofFn x)
  simp only [Circuit.wires,List.length_ofFn,List.length_take,Nat.min_eq_left hj.le] at len
  rw [len]
  rfl

private theorem prefixBeyond (C : Circuit) (j : ℕ) (x : Row n) (i : ℕ)
    (bound : n+j ≤ i) : prefixRead C j x i = false := by
  have len := foldLen (C.gates.take j) (List.ofFn x)
  simp only [List.length_take,List.length_ofFn] at len
  have h : (Circuit.wires ⟨C.gates.take j,0⟩ (List.ofFn x)).length ≤ i := by omega
  change (Circuit.wires ⟨C.gates.take j,0⟩ (List.ofFn x)).getD i false = false
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
  rfl

private theorem redirectNe (top : Row n) (j N : ℕ) (hj : j < N) (i : ℕ) :
    redirect top (n+N) i = n+j ↔ i = n+j := by
  unfold redirect
  split <;> rename_i h
  · split <;> omega
  · rfl

private theorem runCore (C : Circuit) (hc : Monotone2 C) (top x : Row n)
    (j : ℕ) (hj : j ≤ C.gates.length) (i : ℕ) :
    prefixRead (toCore C top) j x (redirect top (n+C.gates.length) i) =
      prefixRead C j (mask top x) i := by
  induction j generalizing i with
  | zero =>
    simp only [prefixRead,Circuit.eval,Circuit.wires,List.take_zero,List.foldl_nil]
    unfold redirect
    split <;> rename_i h
    · cases e : top ⟨i,h⟩ <;> simp [e,mask,List.getD_eq_getElem?_getD,h]
    · simp [List.getD_eq_getElem?_getD,h]
  | succ j ih =>
    have lt : j < C.gates.length := hj
    have lt' : j < (toCore C top).gates.length := by simpa [toCore] using lt
    have prev := ih lt.le
    rw [prefixSucc _ _ lt',prefixSucc _ _ lt]
    simp only [redirectNe top j _ lt]
    split <;> rename_i eq
    · have gate : (toCore C top).gates[j] = gateAt C top ⟨j,lt⟩ := List.getElem_ofFn ..
      rw [gate]
      apply trimVal _ (hc _ (List.getElem_mem _)) _ _ _ _ _ prev
      · apply prefixBeyond; omega
      · intro u
        apply ExtremalVerifier.evalMono (⟨C.gates.take j,u⟩ : Circuit)
          (fun g h => hc g (List.mem_of_mem_take h))
        intro v hv
        exact (Bool.and_eq_true_iff.mp hv).2
    · exact prev i

theorem eval_toCore (C : Circuit) (hc : Monotone2 C) (top x : Row n) :
    (toCore C top).eval (List.ofFn x) = C.eval (List.ofFn (mask top x)) := by
  have h := runCore C hc top x C.gates.length (Nat.le_refl _) C.output
  have size : (toCore C top).gates.length = C.gates.length := by simp [toCore]
  have takeD : (toCore C top).gates.take C.gates.length = (toCore C top).gates := by
    exact List.take_of_length_le size.le
  simp only [prefixRead,takeD,List.take_length,Circuit.eval,Circuit.wires] at h
  exact h

private theorem trimOr (g : Gate) (hg : Legal g) (l : ℕ → Bool) (r : ℕ → ℕ) (b : ℕ) :
    isOr (trim g l r b) = true ↔ isOr g = true ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, l i = true := by
  rcases g with ⟨op,xs⟩
  obtain ⟨hop,len⟩ := hg
  change xs.length ≤ 2 at len
  rcases hop with h | h
  · change op = .and at h
    subst op
    simp [trim,isOr]
  · change op = .or at h
    subst op
    rcases xs with _ | ⟨a,_ | ⟨c,_ | ⟨_,_⟩⟩⟩
    · simp [trim,isOr,copy]
    · simp [trim,isOr,copy]
    · cases ha : l a <;> cases hd : l c <;> simp [trim,isOr,copy,ha,hd]
    · simp at len

private theorem ofFnCount {m : ℕ} (f : Fin m → Gate) :
    (List.ofFn f).countP isOr = (Finset.univ.filter (fun j => isOr (f j) = true)).card := by
  let inds := List.finRange m
  have hu : inds.toFinset = Finset.univ := by ext i; simp [inds]
  rw [← hu, (List.nodup_finRange m).card_eq_countP]
  simp [List.finRange]

/-- A binary OR whose two raw input occurrences are true on the full core. -/
def binaryReady (C : Circuit) (top : Row n) (j : Fin C.gates.length) : Bool :=
  (isOr C.gates[j] && (C.gates[j].inputs.length == 2)) &&
    C.gates[j].inputs.all (prefixRead C j top)

/-- Only original binary ORs with two true raw input occurrences survive. -/
theorem count_toCore (C : Circuit) (hc : Monotone2 C) (top : Row n) :
    (toCore C top).gates.countP isOr =
    (Finset.univ.filter (fun j => binaryReady C top j = true)).card := by
  change (List.ofFn (gateAt C top)).countP isOr = _
  rw [ofFnCount]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  unfold gateAt binaryReady
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,and_assoc]
  exact trimOr C.gates[j] (hc C.gates[j] (List.getElem_mem _)) (prefixRead C j top)
    (redirect top (n+C.gates.length)) (n+C.gates.length)

/-- Any predicate covering the ready ORs supplies an upper bound. This form
allows the caller to use the very same predicate as its chain counting proof. -/
theorem count_toCore_le (C : Circuit) (hc : Monotone2 C) (top : Row n)
    (ready : Fin C.gates.length → Prop) [DecidablePred ready]
    (covers : ∀ j : Fin C.gates.length, isOr C.gates[j] = true →
      (∀ i ∈ C.gates[j].inputs, prefixRead C j top i = true) → ready j) :
    (toCore C top).gates.countP isOr ≤ (Finset.univ.filter ready).card := by
  rw [count_toCore C hc top]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,binaryReady,Bool.and_eq_true,
    beq_iff_eq,List.all_eq_true] at hj ⊢
  exact covers j hj.1.1 hj.2

end Row4201.Restrict
#print axioms Row4201.Restrict.eval_toCore
#print axioms Row4201.Restrict.toCore_mono
#print axioms Row4201.Restrict.count_toCore
#print axioms Row4201.Restrict.count_toCore_le
