import Transfer

namespace FirstFive.Cofactor

def input (m : Fin 512) (i : Fin 9) : Bool := m.val.testBit i.val

def exposes (i : Fin 9) (m : Fin 512) : Bool :=
  !(input m i) && !(target (input m)) && target (Function.update (input m) i true)

def initial (k : Fin 7) (x : Fin 9 → Bool) : Bool :=
  ![!(x 5),x 5 && x 6,x 5 && x 7,x 5 && x 8,x 5 || x 6,x 5 || x 7,x 5 || x 8] k

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem raw_exposed : ∀ (i j : Fin 9), (i=2 ∨ i=3) → i≠j →
    ∃ m : Fin 512, input m j = true ∧ exposes i m = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem initial_exposed : ∀ i : Fin 9, (i=2 ∨ i=3) → ∀ k : Fin 7, k≠3 →
    ∃ m : Fin 512, initial k (input m) = true ∧ exposes i m = true := by decide +kernel

#print axioms initial_exposed
end FirstFive.Cofactor
