import PEqualNP.Outside.L_meta_12184

/-! Transport every unrestricted AND/OR/NOT budget between the literal functions
of L-meta-15174 and L-meta-13131, using the merged dual_size and relabel_size
theorems of L-meta-12184. The permutations and their finite truth identities are
specific to this pair. -/

namespace Row15174Dual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12184.Transfer (dual_size relabel_size)

def f (x : Fin 6 → Bool) := Nat.testBit (3903367336 * 2^32 + 3892348928)
  (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)
def g (x : Fin 6 → Bool) := Nat.testBit (4277074666 * 2^32 + 4277074568)
  (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)
def p : Fin 6 → Fin 6 := ![0, 1, 5, 3, 2, 4]
def q : Fin 6 → Fin 6 := ![0, 1, 4, 3, 5, 2]

set_option maxRecDepth 8192 in
theorem back : ∀ x : Fin 6 → Bool, (!(g (fun i => !x (p i)))) = f x := by decide +kernel
set_option maxRecDepth 8192 in
theorem forth : ∀ x : Fin 6 → Bool, (!(f (fun i => !x (q i)))) = g x := by decide +kernel

theorem budgets (s : ℕ) : HasCircuitSize 6 f s ↔ HasCircuitSize 6 g s := by
  constructor
  · intro hf
    have hd := dual_size f ⟨fun _ => true, by decide +kernel⟩ s hf
    have hg := relabel_size q _ s hd
    change HasCircuitSize 6 (fun x => !(f (fun i => !x (q i)))) s at hg
    rwa [funext forth] at hg
  · intro hg
    have hd := dual_size g ⟨fun _ => true, by decide +kernel⟩ s hg
    have hf := relabel_size p _ s hd
    change HasCircuitSize 6 (fun x => !(g (fun i => !x (p i)))) s at hf
    rwa [funext back] at hf

end Row15174Dual
#print axioms Row15174Dual.budgets
