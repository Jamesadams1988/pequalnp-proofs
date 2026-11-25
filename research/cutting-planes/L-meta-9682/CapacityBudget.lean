import TargetTrace

/-! Size accounting for the live occurrence traces extracted in TargetTrace.
The division and source lower bounds are hypotheses supplied by the target
line and axiom family. The accounting works for every official CP rule. -/
namespace CPTargetTrace

open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch

inductive RuleKind where
  | source | addition | division | multiplication
  deriving DecidableEq

variable {V : Type} [DecidableEq V]

def ruleKind : Rule V → RuleKind
  | .inl _ => .source
  | .inr (.inl _) => .addition
  | .inr (.inr (.inl _)) => .multiplication
  | .inr (.inr (.inr _)) => .division

def countKind (live : Finset ℕ) (rule : ℕ → Rule V) (k : RuleKind) : ℕ :=
  (live.filter (fun i => ruleKind (rule i) = k)).card

private theorem countKindSum (live : Finset ℕ) (rule : ℕ → Rule V) (k : RuleKind) :
    countKind live rule k = ∑ i ∈ live, if ruleKind (rule i) = k then 1 else 0 :=
  (Finset.sum_boole _ _).symm

private theorem unaryIndicator (r : Rule V) :
    (if (parents r).length = 1 then 1 else 0 : ℕ) =
      (if ruleKind r = .division then 1 else 0) +
      (if ruleKind r = .multiplication then 1 else 0) := by
  rcases r with ax | (a | (m | d)) <;> simp [parents, ruleKind]

private theorem countAllKinds (live : Finset ℕ) (rule : ℕ → Rule V) :
    countKind live rule .source + countKind live rule .addition +
    countKind live rule .division + countKind live rule .multiplication = live.card := by
  simp only [countKindSum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ ∈ live, (1 : ℕ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      cases ruleKind (rule i) <;> decide
    _ = _ := by simp

/-- With six necessary sources and two necessary divisions, thirteen live
lines force a tree with five additions, zero multiplications, and one use
for every non-root occurrence (including the source occurrences). Uses count
both inputs of an addition, even when they refer to the same occurrence. -/
theorem capacityBudget {rule : ℕ → Rule V} {live : Finset ℕ} {root : ℕ}
    (member : root ∈ live) (subset : live ⊆ Finset.range (root + 1))
    (closed : closedUnder (fun i => parents (rule i)) live)
    (order : ∀ i j, j ∈ parents (rule i) → j < i)
    (used : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (size : live.card ≤ 13) (sources : 6 ≤ countKind live rule .source)
    (divisions : 2 ≤ countKind live rule .division) :
    live.card = 13 ∧ countKind live rule .source = 6 ∧ countKind live rule .addition = 5 ∧
    countKind live rule .division = 2 ∧ countKind live rule .multiplication = 0 ∧
    ∀ i ∈ live, i ≠ root → uses (fun j => parents (rule j)) live i = 1 := by
  let incoming := fun i => parents (rule i)
  have fan (i : ℕ) : (incoming i).length ≤ 2 := by
    change (parents (rule i)).length ≤ 2
    rcases rule i with ax | (a | (m | d)) <;> simp [parents]
  have budget := count_budget member subset closed used order (fun i _ => fan i)
  have leaves : (live.filter (fun i => (incoming i).length = 0)).card =
      countKind live rule .source := by
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, incoming]
    rcases rule i with ax | (a | (m | d)) <;> simp [parents, ruleKind]
  have unary : (live.filter (fun i => (incoming i).length = 1)).card =
      countKind live rule .division + countKind live rule .multiplication := by
    have countUnary : (∑ i ∈ live, if (incoming i).length = 1 then 1 else 0 : ℕ) =
        (live.filter (fun i => (incoming i).length = 1)).card := Finset.sum_boole _ _
    rw [← countUnary, countKindSum, countKindSum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => unaryIndicator (rule i)
  change live.card + 1 = 2 * (live.filter (fun i => (incoming i).length = 0)).card +
    (live.filter (fun i => (incoming i).length = 1)).card +
    ∑ i ∈ live.erase root, (uses incoming live i - 1) at budget
  rw [leaves, unary] at budget
  have partition := countAllKinds live rule
  have excess : ∑ i ∈ live.erase root, (uses incoming live i - 1) = 0 := by omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro i hi hne
  have positive : 0 < uses incoming live i := uses_pos (used i hi hne)
  have atMost := Finset.single_le_sum (f := fun j => uses incoming live j - 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, hi⟩)
  change uses incoming live i = 1
  omega

end CPTargetTrace

#print axioms CPTargetTrace.capacityBudget
