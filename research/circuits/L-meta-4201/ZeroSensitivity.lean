import PEqualNP.Defs

/-! A false base input and its single-coordinate positive perturbations bound
the number of OR gates in any fan-in-two monotone circuit. Demand sets are
sets of wire indices, so reusing a wire does not duplicate its gate cost. -/
namespace ZeroSensitivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Counts every OR gate, including gates that read fewer than two wires. -/
def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

/-- Only a binary OR can increase the number of demanded input wires. -/
def isBinaryOr (g : Gate) : Bool := isOr g && (g.inputs.length == 2)

private def charge (g : Gate) : ℕ := if isBinaryOr g then 1 else 0
private def gateVal (g : Gate) (w : ℕ → Bool) := g.op.eval (g.inputs.map w)
private def step (w : List Bool) (g : Gate) := w ++ [gateVal g (fun i => w.getD i false)]

private theorem appendRead (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false = if i = w.length then a else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> simp
  | cons b ws ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.getD_cons_succ] using ih i

private theorem parents (g : Gate) (kinds : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (arity : g.inputs.length ≤ 2) (w : ℕ → Bool) (off : gateVal g w = false) :
    ∃ P : Finset ℕ, P.card ≤ 1 + charge g ∧ (∀ i ∈ P, w i = false) ∧
      ∀ y : ℕ → Bool, gateVal g y = true → ∃ i ∈ P, y i = true := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at kinds
  rcases kinds with rfl | rfl
  · have someOff : ∃ i ∈ ins, w i = false := by
      by_contra! allOn
      have yes : (ins.map w).all id = true := by
        apply List.all_eq_true.mpr
        intro a ha
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
        simpa using allOn i hi
      change (ins.map w).all id = false at off
      simp_all
    obtain ⟨i,hi,hw⟩ := someOff
    refine ⟨{i}, by simp [charge,isBinaryOr,isOr], by simpa using hw, ?_⟩
    intro y on
    exact ⟨i, by simp, List.all_eq_true.mp on _ (List.mem_map_of_mem hi)⟩
  · refine ⟨ins.toFinset, ?_, ?_, ?_⟩
    · have h := ins.toFinset_card_le
      change ins.length ≤ 2 at arity
      by_cases len : ins.length = 2
      · simpa [charge,isBinaryOr,isOr,len] using (h.trans arity)
      · have small : ins.toFinset.card ≤ 1 := by omega
        simpa [charge,isBinaryOr,isOr,len] using small
    · intro i hi
      have hi' := List.mem_toFinset.mp hi
      by_contra! isOn
      have wi : w i = true := by simpa using isOn
      have yes : (ins.map w).any id = true :=
        List.any_eq_true.mpr ⟨w i, List.mem_map_of_mem hi', wi⟩
      change (ins.map w).any id = false at off
      simp_all
    · intro y on
      obtain ⟨a,ha,truth⟩ := List.any_eq_true.mp on
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact ⟨i,List.mem_toFinset.mpr hi,truth⟩

variable {n : ℕ}
private abbrev Row (n : ℕ) := Fin n → Bool
private def Bound (x : Row n) (S : Finset (Fin n)) (w : Row n → List Bool) (k : ℕ) :=
  ∀ D : Finset ℕ, (∀ i ∈ D, (w x).getD i false = false) →
    (∀ v ∈ S, ∃ i ∈ D, (w (Function.update x v true)).getD i false = true) →
    S.card ≤ D.card + k

private theorem advance {x : Row n} {S : Finset (Fin n)} {w : Row n → List Bool}
    {k : ℕ} (prev : Bound x S w k) (lengths : ∀ y, (w y).length = (w x).length)
    (g : Gate) (kinds : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : Bound x S (fun y => step (w y) g) (k + charge g) := by
  intro D hfalse htrue
  let key := (w x).length
  have read (y : Row n) (i : ℕ) : (step (w y) g).getD i false =
      if i = key then gateVal g (fun a => (w y).getD a false) else (w y).getD i false := by
    rw [step, appendRead, lengths y]
  by_cases hk : key ∈ D
  · have off := hfalse key hk
    rw [read, ite_eq_left rfl] at off
    obtain ⟨P,pc,pOff,pOn⟩ := parents g kinds arity _ off
    let E := D.erase key ∪ P
    have priorBound := prev E (by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hi
        simpa only [read, ite_eq_right hne] using hfalse i hm
      · exact pOff i hi) (by
      intro v hv
      obtain ⟨i,hi,on⟩ := htrue v hv
      rw [read] at on
      by_cases he : i = key
      · rw [ite_eq_left he] at on
        obtain ⟨a,ha,hw⟩ := pOn _ on
        exact ⟨a,Finset.mem_union_right _ ha,hw⟩
      · exact ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hi⟩), by simpa [he] using on⟩)
    have cardE : E.card ≤ (D.erase key).card + P.card := Finset.card_union_le _ _
    have cardD := Finset.card_erase_add_one hk
    omega
  · have priorBound := prev D (by
      intro i hi
      have hne : i ≠ key := fun h => hk (h ▸ hi)
      simpa only [read, ite_eq_right hne] using hfalse i hi) (by
      intro v hv
      obtain ⟨i,hi,on⟩ := htrue v hv
      have hne : i ≠ key := fun h => hk (h ▸ hi)
      exact ⟨i,hi,by simpa only [read, ite_eq_right hne] using on⟩)
    omega

private theorem run {x : Row n} {S : Finset (Fin n)} (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : Row n → List Bool) (lengths : ∀ y, (w y).length = (w x).length)
    (k : ℕ) (prev : Bound x S w k) :
    Bound x S (fun y => gs.foldl step (w y)) (k + gs.countP isBinaryOr) := by
  induction gs generalizing w k with
  | nil => simpa using prev
  | cons g gs ih =>
    have hg := h g (by simp)
    have hw := advance prev lengths g hg.1 hg.2
    have hl : ∀ y, (step (w y) g).length = (step (w x) g).length := by
      intro y; simp [step,lengths y]
    have rest := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _ hl _ hw
    simpa [List.countP_cons,charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

private theorem initial (x : Row n) (S : Finset (Fin n)) :
    Bound x S List.ofFn 0 := by
  intro D off on
  have covered : S.image Fin.val ⊆ D := by
    intro i hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,yes⟩ := on v hv
    have no := off j hj
    by_cases hn : j < n
    · have y : Function.update x v true ⟨j,hn⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn,hn] using yes
      have z : x ⟨j,hn⟩ = false := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn,hn] using no
      by_cases same : (⟨j,hn⟩ : Fin n) = v
      · simpa [←same] using hj
      · simp [Function.update_of_ne same,z] at y
    · simp [List.getD_eq_getElem?_getD,hn] at yes
  simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card covered

theorem binaryOrCountBound (C : Circuit) (hm : Monotone2 C) (x : Fin n → Bool) (S : Finset (Fin n))
    (base : C.eval (List.ofFn x) = false)
    (flip : ∀ v ∈ S, C.eval (List.ofFn (Function.update x v true)) = true) :
    S.card ≤ C.gates.countP isBinaryOr + 1 := by
  have b := run C.gates hm List.ofFn (fun _ => by simp) 0 (initial x S)
  have z := b {C.output} (by
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    exact base) (by
    intro v hv
    exact ⟨C.output,by simp,flip v hv⟩)
  simpa [Nat.add_comm] using z

theorem orCountBound (C : Circuit) (hm : Monotone2 C) (x : Fin n → Bool) (S : Finset (Fin n))
    (base : C.eval (List.ofFn x) = false)
    (flip : ∀ v ∈ S, C.eval (List.ofFn (Function.update x v true)) = true) :
    S.card ≤ C.gates.countP isOr + 1 := by
  have mono : C.gates.countP isBinaryOr ≤ C.gates.countP isOr :=
    List.countP_mono_left (fun g _ hg => by
      cases h : isOr g <;> simp_all [isBinaryOr])
  exact (binaryOrCountBound C hm x S base flip).trans (Nat.add_le_add_right mono 1)

end ZeroSensitivity
#print axioms ZeroSensitivity.binaryOrCountBound
#print axioms ZeroSensitivity.orCountBound
