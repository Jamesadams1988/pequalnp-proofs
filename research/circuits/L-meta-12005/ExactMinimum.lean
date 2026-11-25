import Witness
import PEqualNP.Outside.L_meta_4795
import PEqualNP.Outside.L_meta_9526

/-!
The two restrictions at the first input may have different costs. The first elimination
chooses the polarity. The second elimination works for either choice and reaches a common
cofactor. Applying this argument to the seven-input graph in L-meta-12005 gives its exact
minimum. The monotone upper bound comes from James Adams's 11-gate witness in this folder.
The elimination and relabeling lemmas in L-meta-4795 credit sanchan's L-meta-927.
The four-clique bound comes from hilelyos's L-meta-9526.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4795_aux

namespace LeafTransfer

def pin {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool)
    (x : Fin n → Bool) : Bool :=
  f (Function.update x p b)

def essential {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x, f (Function.update x p (!x p)) ≠ f x

def nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

/-- If each restriction at p admits the same essential pin at q with a common
nonconstant result, the resulting function saves three gates. -/
theorem threeGateRestriction {n s : ℕ} {f core : (Fin (n+1) → Bool) → Bool}
    {p q : Fin (n+1)} {value : Bool}
    (hp : essential f p) (hq : ∀ b, essential (pin f p b) q)
    (common : ∀ b, pin (pin f p b) q value = core)
    (nc : nonconstant core) (c : HasCircuitSize (n+1) f s) :
    ∃ t, t+3 ≤ s ∧ HasCircuitSize (n+1) core t := by
  have restricted_nc (b : Bool) : nonconstant (pin (pin f p b) q value) := by
    rw [common b]
    exact nc
  have branch_nc (b : Bool) : nonconstant (pin f p b) := by
    obtain ⟨x, y, hxy⟩ := restricted_nc b
    exact ⟨Function.update x q value, Function.update y q value, hxy⟩
  obtain ⟨b, r, hr, cr⟩ := gate_elim_at n f p s hp branch_nc c
  obtain ⟨t, ht, ct⟩ := one_gate_at n (pin f p b) q value r (hq b) (restricted_nc b) cr
  exact ⟨t, by omega, (common b) ▸ ct⟩

end LeafTransfer

namespace L12005Minimum

open LeafTransfer Local.CounterexampleTest
open PEqualNP.Outside.L_meta_9526 (targetK4 lb_K4)

/-- On vertices 1, 2, 4, 5 and 6, the surviving graph contains every edge except 1–2. -/
private def core (x : Fin 7 → Bool) : Bool :=
  ((x 1 || x 2) && (x 4 || x 5 || x 6)) ||
    (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)

set_option maxRecDepth 16000 in
private theorem commonCore (b : Bool) : pin (pin target 3 b) 0 false = core := by
  funext x
  revert x
  cases b <;> decide +kernel

theorem lower {s : ℕ} (c : HasCircuitSize 7 target s) : 11 ≤ s := by
  have leaf : essential target 3 :=
    ⟨fun i => decide (i = 0), by decide +kernel⟩
  have neighbor (b : Bool) : essential (pin target 3 b) 0 := by
    refine ⟨fun i => decide (i = 4), ?_⟩
    cases b <;> decide +kernel
  have nc : nonconstant core :=
    ⟨fun _ => false, fun i => decide (i = 4 ∨ i = 5), by decide +kernel⟩
  obtain ⟨r, hr, cr⟩ := threeGateRestriction leaf neighbor commonCore nc c
  have dep : essential core 1 := ⟨fun i => decide (i = 4), by decide +kernel⟩
  have stays : nonconstant (pin core 1 false) :=
    ⟨fun _ => false, fun i => decide (i = 4 ∨ i = 5), by decide +kernel⟩
  obtain ⟨t, ht, ct⟩ := one_gate_at 6 core 1 false r dep stays cr
  -- The four coordinates are original vertices 2, 4, 5 and 6.
  let label : Fin 7 → Fin 4 := ![0,0,0,0,1,2,3]
  have ck := relabel_size label (pin core 1 false) t ct
  have eqn : (fun x : Fin 4 → Bool => pin core 1 false (x ∘ label)) = targetK4 :=
    funext (by decide +kernel)
  rw [eqn] at ck
  have := lb_K4 t ck
  omega

/-- The same monotone circuit attains the unrestricted minimum. -/
theorem exactMinimum :
    HasCircuitSize 7 target 11 ∧
    (∀ s, HasCircuitSize 7 target s → 11 ≤ s) ∧
    (∃ C : Circuit, Monotone2 C ∧ C.size = 11 ∧ ∀ x : Fin 7 → Bool,
       C.eval (List.ofFn x) = target x) := by
  let C : Circuit := ⟨witness, 17⟩
  have mono : Monotone2 C := by
    intro g hg
    exact basis g hg
  have legal : FanInTwo C := by
    intro g hg
    obtain ⟨hop, har⟩ := basis g hg
    exact ⟨hop.elim Or.inl (fun h => Or.inr (Or.inl h)), har⟩
  exact ⟨⟨C, legal, le_rfl, witness_correct⟩, fun _ => lower, C, mono, rfl, witness_correct⟩

end L12005Minimum

#print axioms LeafTransfer.threeGateRestriction
#print axioms L12005Minimum.exactMinimum
