import IncidenceTransfer
import Restriction
import PEqualNP.Outside.L_meta_4795

/-! Size-preserving deletion and a twelve-gate black-box restoration.
The relabeling of arbitrary wire indices uses nicohabets's L-meta-4795,
which credits sanchan's L-meta-927. The two five-edge blocks use the
project's CoverCircuitList constructor. -/
namespace Row9802.Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit
open PEqualNP.Outside.L_meta_4795_aux (relabel relGate rel_fold rel_init)
open Row4201.PGSequence (accepts)

private theorem relabelMono {n m} (p : Fin n → Fin m) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (relabel n m p C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h a ha).1, by simpa [relGate] using (h a ha).2⟩

private theorem evalRelabel {n m} (p : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m p C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) :=
  (rel_fold n m p C.gates _ _ (rel_init n m p x)).2.2 C.output

/-- Pin the deleted pair to false, then relabel the remaining forty inputs.
Each original gate has one representative, so the construction preserves size. -/
theorem delete (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x, C.eval (List.ofFn x) = true ↔ accepts x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      ∀ x : Fin 40 → Bool, D.eval (List.ofFn x) = true ↔ small x := by
  let R := Row4201.Restrict.toCore C kept
  refine ⟨relabel 42 40 back R,relabelMono _ _ (Row4201.Restrict.toCore_mono C hm kept),?_,?_⟩
  · simp [Circuit.size,relabel,R,Row4201.Restrict.toCore]
  · intro x
    rw [evalRelabel,Row4201.Restrict.eval_toCore C hm, hc]
    exact onKept x

private def adjoin {n} (C : Circuit) (c f : Fin n) (t : List (Fin n)) : Circuit :=
  let s := n + C.size
  let b := blockGates s (c.val,f.val :: t.map Fin.val)
  ⟨(C.gates ++ b) ++ [⟨.or,[C.output,s+t.length]⟩],s+t.length+1⟩

private theorem adjoinSize {n} (C : Circuit) (c f : Fin n) (t : List (Fin n)) :
    (adjoin C c f t).size = C.size + t.length + 2 := by
  simp [adjoin,Circuit.size,blockGates_length,Nat.add_assoc]

private theorem adjoinMono {n} (C : Circuit) (hc : Monotone2 C) (c f : Fin n) (t : List (Fin n)) :
    Monotone2 (adjoin C c f t) := by
  intro g hg
  change g ∈ (_ ++ _) ++ [_] at hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with (h | h) | rfl
  · exact hc g h
  · obtain ⟨op,arity⟩ := blockGates_ops _ _ _ h
    exact ⟨op.symm,arity.le⟩
  · simp

private theorem adjoinOutput {n} (C : Circuit) (c f : Fin n) (t : List (Fin n)) :
    (adjoin C c f t).output < n + (adjoin C c f t).size := by
  rw [adjoinSize]
  change n + C.size + t.length + 1 < _
  omega

private theorem adjoinEval {n} (C : Circuit) (valid : C.output < n + C.size)
    (c f : Fin n) (t : List (Fin n)) (x : Fin n → Bool) :
    (adjoin C c f t).eval (List.ofFn x) = true ↔
      C.eval (List.ofFn x) = true ∨ star x c f t := by
  let w := run C.gates (List.ofFn x)
  let s := n+C.size
  let b := blockGates s (c.val,f.val::t.map Fin.val)
  let z := run b w
  have wl : w.length = s := by simp [w,s,Circuit.size,run_length]
  have zl : z.length = s+t.length+1 := by simp [z,b,run_length,wl,blockGates_length,Nat.add_assoc]
  have inside (i : Fin n) : i.val < s := by dsimp [s]; omega
  have boundTail : ∀ v ∈ t.map Fin.val, v < s := by
    intro v hv; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv; exact inside i
  have rd (i : Fin n) : w.getD i.val false = x i := by
    rw [show w = run C.gates (List.ofFn x) by rfl, getD_run _ _ _ (by simp)]
    exact getD_ofFn x i.val i.isLt
  have bh := blockGates_eval s c.val f.val (t.map Fin.val) w wl (inside c) (inside f) boundTail
  change z.getD (s+(t.map Fin.val).length) false = _ at bh
  simp only [List.length_map] at bh
  have keepout : z.getD C.output false = C.eval (List.ofFn x) :=
    getD_run b w _ (by rwa [wl])
  change (run ((C.gates ++ b) ++ [⟨GateOp.or,[C.output,s+t.length]⟩]) (List.ofFn x)).getD
    (s+t.length+1) false = true ↔ _
  rw [run_append,run_append,run_singleton]
  change (z ++ [_]).getD (s+t.length+1) false = true ↔ _
  rw [←zl,getD_snoc_length]
  change GateOp.or.eval [z.getD C.output false, z.getD (s+t.length) false] = true ↔ _
  rw [eval_or2]
  have tail : (t.map Fin.val).any (fun v => w.getD v false) = t.any x := by
    rw [List.any_map]
    exact any_congr_mem _ _ _ (fun v _ => rd v)
  rw [keepout,bh,rd c,rd f,tail]
  simp [star]

private theorem outputValid (D : Circuit) {n} (h : ∃ y : Fin n → Bool, D.eval (List.ofFn y) = true) :
    D.output < n+D.size := by
  obtain ⟨y,hy⟩ := h
  by_contra! bad
  change (run D.gates (List.ofFn y)).getD D.output false = true at hy
  rw [List.getD_eq_default _ _ (by simpa [run_length,Circuit.size] using bad)] at hy
  contradiction

/-- Restore the two disjoint five-edge stars, keeping the punctured
circuit untouched. Its output and the two star values are combined by OR. -/
theorem restore (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 40 → Bool, C.eval (List.ofFn x) = true ↔ small x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size+12 ∧
      ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ accepts x := by
  let C0 := relabel 40 42 emb C
  let C1 := adjoin C0 0 21 pointTail
  let C2 := adjoin C1 22 1 lineTail
  have h0 : Monotone2 C0 := relabelMono emb C hm
  have computes0 (x : Fin 42 → Bool) : C0.eval (List.ofFn x) = true ↔ small (x ∘ emb) := by
    rw [evalRelabel]; exact hc _
  have valid : C0.output < 42+C0.size := outputValid C0 ⟨fun _ => true,(computes0 _).mpr
    ⟨0,20,by decide +kernel,rfl,rfl⟩⟩
  refine ⟨C2,adjoinMono _ (adjoinMono _ h0 _ _ _) _ _ _,?_,?_⟩
  · change (adjoin (adjoin C0 0 21 pointTail) 22 1 lineTail).size = _
    rw [adjoinSize,adjoinSize]
    simp [C0,relabel,Circuit.size,pointTail,lineTail,Nat.add_assoc]
  · intro x
    rw [show C2 = adjoin C1 22 1 lineTail from rfl,
      adjoinEval C1 (adjoinOutput C0 0 21 pointTail),
      show C1 = adjoin C0 0 21 pointTail from rfl,adjoinEval C0 valid,
      computes0,decomposition,or_assoc]

end Row9802.Transfer
#print axioms Row9802.Transfer.delete
#print axioms Row9802.Transfer.restore
