import PEqualNP.Defs
/-! Monotone witness circuits for every single-coordinate face of L-meta-12096.
Each certificate evaluates its circuit against the specified restriction on all
32 assignments. The independent C++ replay tests minimality. -/
namespace Row12096Faces
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def target (x : Fin 6 → Bool) := Nat.testBit (4269866496 * 2^32 + 4261472256)
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def face (p : Fin 6) (b : Bool) (x : Fin 5 → Bool) := target (p.insertNth b x)
def size (p : Fin 6) (b : Bool) : ℕ :=
  if b then ![8,8,8,8,7,7] p else ![6,6,6,4,8,8] p
def ce0e0e080 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [9, 6]⟩], 10⟩
def cf8f0f0e0 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [11, 8]⟩], 12⟩
def c80000000 : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [5, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [7, 4]⟩], 8⟩
def cfefefee8 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [11, 10]⟩], 12⟩
def cfe00e800 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [11, 7]⟩], 12⟩
def cfe80fe00 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [4, 0]⟩, ⟨.and, [8, 1]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [10, 7]⟩], 11⟩
def witness (p : Fin 6) (b : Bool) : Circuit :=
  if b then ![cf8f0f0e0, cf8f0f0e0, cf8f0f0e0, cfefefee8, cfe80fe00, cfe80fe00] p
  else ![ce0e0e080, ce0e0e080, ce0e0e080, c80000000, cfe00e800, cfe00e800] p

set_option maxRecDepth 8192 in
theorem upper (p : Fin 6) (b : Bool) : Monotone2 (witness p b) ∧
    (witness p b).size = size p b ∧
    ∀ x : Fin 5 → Bool, (witness p b).eval (List.ofFn x) = face p b x := by
  fin_cases p <;> cases b <;> refine ⟨?_, rfl, ?_⟩
  all_goals first | decide +kernel | simp [witness, Monotone2, ce0e0e080, cf8f0f0e0, c80000000, cfefefee8, cfe00e800, cfe80fe00]

end Row12096Faces
#print axioms Row12096Faces.upper
