import PEqualNP.MetaComplexity.Helpers.Support

namespace Row12096Features
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- An essential transition for each input forces a support of size n, even
when both endpoints of every transition must lie in a prescribed domain. -/
theorem essentialOn_lower {n : ℕ} (domain : (Fin n → Bool) → Prop)
    (f : (Fin n → Bool) → Bool)
    (essential : ∀ i, ∃ x, domain x ∧ domain (Function.update x i (!x i)) ∧
      f (Function.update x i (!x i)) ≠ f x)
    (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, domain x → C.eval (List.ofFn x) = f x) : n ≤ C.size + 1 := by
  let computed (x : Fin n → Bool) := C.eval (List.ofFn x)
  have depends : ∀ i, ∃ x, computed (Function.update x i (!x i)) ≠ computed x := by
    intro i
    obtain ⟨x, hx, hy, hne⟩ := essential i
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn (Function.update x i (!x i))) ≠ C.eval (List.ofFn x)
    rw [correct _ hy, correct _ hx]
    exact hne
  exact Helpers.dep_lower n computed depends C.size ⟨C, legal, le_rfl, fun _ => rfl⟩

abbrev Input := Fin 6 → Bool

/-- A1, A2 and A3 threshold the first three bits. B1 and B2 threshold the
last two. The fourth coordinate is the original bit d. -/
def features (x : Input) : Input :=
  ![x 0 || x 1 || x 2, (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2),
    x 0 && x 1 && x 2, x 3, x 4 || x 5, x 4 && x 5]

def combine (z : Input) : Bool :=
  (z 3 && (z 1 || (z 0 && z 4))) || (z 2 && z 5)

def posted (x : Input) : Bool :=
  Nat.testBit (4269866496 * 2 ^ 32 + 4261472256)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem factorization : ∀ x, combine (features x) = posted x := by decide +kernel

def bits (v : ℕ) (i : Fin 6) : Bool := v.testBit i
def before : Fin 6 → ℕ := ![24, 9, 51, 3, 9, 23]
def after : Fin 6 → ℕ := ![25, 11, 55, 11, 25, 55]

/-- Each pair consists of two original input assignments. Their feature vectors
differ at the indicated coordinate, and the desired outputs differ. -/
theorem witnessPairs : ∀ i : Fin 6,
    Function.update (features (bits (before i))) i (!(features (bits (before i)) i)) =
      features (bits (after i)) ∧
    combine (features (bits (after i))) ≠ combine (features (bits (before i))) := by
  decide +kernel

/-- The circuit receives the six aggregate signals as its only inputs. -/
theorem combine_lower (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn (features x)) = posted x) : 5 ≤ C.size := by
  have essential : ∀ i : Fin 6, ∃ z,
      z ∈ Set.range features ∧ Function.update z i (!z i) ∈ Set.range features ∧
      combine (Function.update z i (!z i)) ≠ combine z := by
    intro i
    obtain ⟨hflip, hvalue⟩ := witnessPairs i
    refine ⟨features (bits (before i)), ⟨_, rfl⟩, ?_, ?_⟩
    · exact ⟨bits (after i), hflip.symm⟩
    · simpa only [hflip] using hvalue
  have bound := essentialOn_lower (fun z => z ∈ Set.range features) combine essential C legal
    (fun _ ⟨x, hx⟩ => hx ▸ (correct x).trans (factorization x).symm)
  omega

/-- The five gates combine A1, A2, A3, d, B1, B2 in that wire order. -/
def combineCircuit : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 7]⟩,
    ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩

theorem combine_exact :
    Monotone2 combineCircuit ∧ combineCircuit.size = 5 ∧
    (∀ z : Input, combineCircuit.eval (List.ofFn z) = combine z) ∧
    (∀ x, combineCircuit.eval (List.ofFn (features x)) = posted x) ∧
    ∀ C : Circuit, FanInTwo C →
      (∀ x, C.eval (List.ofFn (features x)) = posted x) → 5 ≤ C.size := by
  have evaluates : ∀ z : Input, combineCircuit.eval (List.ofFn z) = combine z := by
    decide +kernel
  exact ⟨by simp [Monotone2, combineCircuit], rfl, evaluates,
    fun x => (evaluates (features x)).trans (factorization x), combine_lower⟩

end Row12096Features

#print axioms Row12096Features.essentialOn_lower
#print axioms Row12096Features.factorization
#print axioms Row12096Features.witnessPairs
#print axioms Row12096Features.combine_lower
#print axioms Row12096Features.combine_exact
