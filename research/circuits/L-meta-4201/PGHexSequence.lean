import PGSequence

/-! Beginning with three points and their three pairwise joins gives an induced six-cycle.
The 36 remaining vertices are added in the same cyclic order as PGSequence, skipping the
six core vertices. Every newly added vertex is adjacent to its predecessor in the full cycle.
-/
namespace Row4201.PGHexSequence
open Row4201.PGSequence PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Local coordinates 0,1,2 are points and 3,4,5 are the lines through their respective pairs. -/
def embedding : Fin 6 → Fin 42 := ![0,1,2,28,21,22]

def embedInput (x : Fin 6 → Bool) (v : Fin 42) : Bool :=
  if v=0 then x 0 else if v=1 then x 1 else if v=2 then x 2 else
  if v=28 then x 3 else if v=21 then x 4 else if v=22 then x 5 else false

def cycleAccepts (x : Fin 6 → Bool) : Bool :=
  (x 0 && (x 3 || x 4)) || (x 1 && (x 4 || x 5)) || (x 2 && (x 5 || x 3))

def nextRank (k : ℕ) : ℕ := if k < 10 then k+5 else k+6

def pref (k : ℕ) (v : Fin 42) : Bool := decide (rank v = 15 ∨ rank v < nextRank k)

def pair (k : Fin 36) (v : Fin 42) : Bool :=
  decide (rank v + 1 = nextRank k.val ∨ rank v = nextRank k.val)

private theorem nextMono {i j} (h : i ≤ j) : nextRank i ≤ nextRank j := by
  unfold nextRank; split_ifs <;> omega
private theorem nextSucc (i : ℕ) : nextRank i < nextRank (i+1) := by
  unfold nextRank; split_ifs <;> omega

theorem prefixMono {i j : ℕ} (h : i ≤ j) (v : Fin 42) (hv : pref i v = true) : pref j v = true := by
  simp only [pref,decide_eq_true_eq] at *
  have := nextMono h
  omega

theorem pairNext (k : Fin 36) (v : Fin 42) (hv : pair k v = true) : pref (k.val+1) v = true := by
  simp only [pref,pair,decide_eq_true_eq] at *
  have := nextSucc k.val
  omega

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem embeddingInjective : Function.Injective embedding := by decide +kernel

theorem embedAt : ∀ (x : Fin 6 → Bool) i, embedInput x (embedding i) = x i := by decide +kernel

theorem coreTest : ∀ v, embedInput (fun _ => true) v = pref 0 v := by decide +kernel

theorem embedBelowCore : ∀ (x : Fin 6 → Bool) v, embedInput x v = true → pref 0 v = true := by decide +kernel

theorem induced : ∀ x, accepts (embedInput x) ↔ cycleAccepts x = true := by decide +kernel

theorem prefixAccepts (k : Fin 36) : accepts (pref k.val) := by
  refine ⟨0,21,by decide,?_,?_⟩ <;> simp [pref,rank,nextRank] <;> split_ifs <;> omega

theorem pairAccepts : ∀ k : Fin 36, accepts (pair k) := by decide +kernel

theorem meetRejects : ∀ k : Fin 36, ¬ accepts (fun v => pref k.val v && pair k v) := by decide +kernel

theorem samples (C : Circuit) (hf : ∀ x, C.eval (List.ofFn x) = true ↔ accepts x) (k : Fin 36) :
    C.eval (List.ofFn (pref k.val)) = true ∧ C.eval (List.ofFn (pair k)) = true ∧
    C.eval (List.ofFn (fun v => pref k.val v && pair k v)) = false := by
  refine ⟨(hf _).mpr (prefixAccepts k), (hf _).mpr (pairAccepts k), ?_⟩
  cases he : C.eval (List.ofFn (fun v => pref k.val v && pair k v)) with
  | false => rfl
  | true => exact (meetRejects k ((hf _).mp he)).elim

theorem computesCore (C : Circuit) (hf : ∀ x, C.eval (List.ofFn x) = true ↔ accepts x)
    (x : Fin 6 → Bool) : C.eval (List.ofFn (embedInput x)) = cycleAccepts x := by
  exact Bool.eq_iff_iff.mpr ((hf _).trans (induced x))

end Row4201.PGHexSequence
#print axioms Row4201.PGHexSequence.samples
#print axioms Row4201.PGHexSequence.computesCore
