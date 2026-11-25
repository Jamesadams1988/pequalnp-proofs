import PEqualNP.Defs

namespace PG4Separation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def prefixRead {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (⟨C.gates.take j,i⟩ : Circuit).eval (List.ofFn x)

private def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) := w ++ [value w g]

private abbrev Safe (a b c : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true → c.getD i false = true

private abbrev Cross (a b : List Bool) (g : Gate) : Prop :=
  ∃ u v, g.op = .or ∧ (g.inputs = [u,v] ∨ g.inputs = [v,u]) ∧
    a.getD u false = true ∧ b.getD u false = false ∧ a.getD v false = false ∧ b.getD v false = true

private theorem gateStep (a b c : List Bool) (S : Safe a b c) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (length : g.inputs.length ≤ 2)
    (bad : ¬ Cross a b g) (ha : value a g = true) (hb : value b g = true) :
    value c g = true := by
  rcases op with hand | hor
  · simp [value,hand,GateOp.eval] at ha hb ⊢
    exact fun i mem => S i (ha i mem) (hb i mem)
  · cases he : g.inputs with
    | nil => simp [value,hor,he,GateOp.eval] at ha
    | cons i rest =>
      cases rest with
      | nil =>
        simp [value,hor,he,GateOp.eval] at ha hb ⊢
        exact S i ha hb
      | cons j tail =>
        cases tail with
        | cons k tail => simp [he] at length
        | nil =>
          simp [value,hor,he,GateOp.eval] at ha hb ⊢
          rcases ha with ai | aj <;> rcases hb with bi | bj
          · exact Or.inl (S i ai bi)
          · by_cases bb : b.getD i false = true
            · exact Or.inl (S i ai bb)
            by_cases aa : a.getD j false = true
            · exact Or.inr (S j aa bj)
            exact (bad ⟨i,j,hor,Or.inl he,ai,by simpa using bb,by simpa using aa,bj⟩).elim
          · by_cases bb : b.getD j false = true
            · exact Or.inr (S j aj bb)
            by_cases aa : a.getD i false = true
            · exact Or.inl (S i aa bi)
            exact (bad ⟨j,i,hor,Or.inr he,aj,by simpa using bb,by simpa using aa,bi⟩).elim
          · exact Or.inr (S j aj bj)

private theorem readAppend (a : List Bool) (x : Bool) (i : ℕ) :
    (a ++ [x]).getD i false = if i < a.length then a.getD i false
      else if i = a.length then x else false := by
  induction a generalizing i with
  | nil => cases i <;> simp
  | cons y a ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

private theorem findCross (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (a b c : List Bool) (ab : a.length = b.length) (ac : a.length = c.length)
    (safe : Safe a b c) (bad : ¬ Safe (gs.foldl step a) (gs.foldl step b) (gs.foldl step c)) :
    ∃ pre g post, gs = pre ++ g :: post ∧ Cross (pre.foldl step a) (pre.foldl step b) g := by
  induction gs generalizing a b c with
  | nil => exact (bad safe).elim
  | cons g rest ih =>
    by_cases cross : Cross a b g
    · exact ⟨[],g,rest,rfl,cross⟩
    have s : Safe (step a g) (step b g) (step c g) := by
      intro i
      simp only [step,readAppend,← ab,← ac]
      have hgate := gateStep a b c safe g (legal g List.mem_cons_self).1
        (legal g List.mem_cons_self).2 cross
      split_ifs <;> first | exact safe i | exact hgate | simp
    obtain ⟨pre,h,post,heq,hit⟩ := ih (fun v hv => legal v (List.mem_cons_of_mem _ hv))
      (step a g) (step b g) (step c g) (by simp [step,ab]) (by simp [step,ac]) s bad
    exact ⟨g::pre,h,post,by rw [heq]; rfl,hit⟩

/-- A circuit true at both inputs and false at their meet has an OR gate that
routes the two inputs through opposite operands. Reads use the bank before
the gate, including the usual false default for an out-of-range read. -/
theorem separatingOR {n : ℕ} (C : Circuit) (hm : Monotone2 C) (a b : Fin n → Bool)
    (ha : C.eval (List.ofFn a) = true) (hb : C.eval (List.ofFn b) = true)
    (hab : C.eval (List.ofFn (fun i => a i && b i)) = false) :
    ∃ j g u v, C.gates[j]? = some g ∧ g.op = .or ∧ (g.inputs = [u,v] ∨ g.inputs = [v,u]) ∧
      prefixRead C j a u = true ∧ prefixRead C j b u = false ∧
      prefixRead C j a v = false ∧ prefixRead C j b v = true := by
  have init : Safe (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i && b i) := by
    intro i
    by_cases hi : i < n
    · simp [List.getD_eq_getElem?_getD,hi]
      exact fun x y => ⟨x,y⟩
    · simp [List.getD_eq_getElem?_getD,hi]
  have fail : ¬ Safe (C.gates.foldl step (List.ofFn a)) (C.gates.foldl step (List.ofFn b))
      (C.gates.foldl step (List.ofFn fun i => a i && b i)) := by
    intro all
    exact Bool.false_ne_true (hab.symm.trans (all C.output ha hb))
  obtain ⟨pre,g,post,split,u,v,hor,hinput,sides⟩ := findCross C.gates hm _ _ _ (by simp) (by simp) init fail
  refine ⟨pre.length,g,u,v,?_,hor,hinput,?_⟩
  · simp [split]
  · have hpre : C.gates.take pre.length = pre := by simp [split]
    unfold prefixRead
    rw [hpre]
    exact sides

end PG4Separation
#print axioms PG4Separation.separatingOR
