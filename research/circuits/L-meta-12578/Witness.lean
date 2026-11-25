import PEqualNP.Defs

namespace Split12578

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372968 * 2 ^ 32 + 3941133032)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

/-- The first AND combines inputs four and five. Subsequent gates use its value
    exactly as the fifth input of the core function. -/
def nine : Circuit :=
  ⟨[⟨.and, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [2, 7]⟩,
    ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [10, 13]⟩], 14⟩

theorem nine_mono : Monotone2 nine := by simp [nine, Monotone2]
theorem nine_size : nine.size = 9 := rfl
theorem nine_eval : ∀ x : Fin 6 → Bool, nine.eval (List.ofFn x) = table x := by decide +kernel

def core (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 4008372968 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def joinLast (x : Fin 6 → Bool) : Fin 5 → Bool :=
  Fin.snoc (fun i : Fin 4 => x i.castSucc.castSucc) (x 4 && x 5)

theorem is_split : ∀ x, table x = core (joinLast x) := by decide +kernel
theorem pin_last : ∀ x : Fin 5 → Bool, table (Fin.snoc x true) = core x := by decide +kernel

end Split12578
