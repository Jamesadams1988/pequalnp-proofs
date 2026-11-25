import ExactMinimum
import PEqualNP.Outside.L_meta_12184

/-!
A butterfly graph has two triangles sharing one vertex. Its edge function
accepts if both endpoints of some edge are true. Adding a sixth input by OR
gives the dual of L-meta-15094. L-meta-13203 uses the same graph with two
vertex labels interchanged. The exact bound in this file comes from
Row15094.exactMinimum. Budget-preserving duality and input relabeling come
from the merged L-meta-12184.
-/
namespace Row15094Butterfly
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12184.Transfer (dual_size relabel_size)

abbrev Fn := (Fin 6 → Bool) → Bool

def graph (x : Fin 6 → Bool) : Bool :=
  x 0 || (x 1 && (x 2 || x 3 || x 4 || x 5)) || (x 2 && x 3) || (x 4 && x 5)

def dual (f : Fn) (x : Fin 6 → Bool) := !(f (fun i => !x i))

set_option maxRecDepth 8192 in
theorem graph_dual : ∀ x, dual graph x = Row15094.f x := by decide +kernel

set_option maxRecDepth 8192 in
theorem posted_dual : ∀ x, dual Row15094.f x = graph x := by decide +kernel

def table13203 (x : Fin 6 → Bool) := Nat.testBit (4294901502 * 2^32 + 4293848810)
    (∑ i : Fin 6, if x i then 2^(i : Nat) else 0)

set_option maxRecDepth 8192 in
theorem sibling : ∀ x, table13203 x = graph (x ∘ ![0, 1, 4, 3, 2, 5]) := by decide +kernel

def form (flipped : Bool) : Fn := if flipped then graph else Row15094.f

theorem base_budgets (flipped : Bool) (s : ℕ) :
    HasCircuitSize 6 (form flipped) s ↔ HasCircuitSize 6 Row15094.f s := by
  cases flipped
  · rfl
  · change HasCircuitSize 6 graph s ↔ HasCircuitSize 6 Row15094.f s
    constructor
    · intro h
      have hd := dual_size graph ⟨fun _ => true, by decide⟩ s h
      change HasCircuitSize 6 (dual graph) s at hd
      rwa [funext graph_dual] at hd
    · intro h
      have hd := dual_size Row15094.f ⟨fun _ => true, by decide +kernel⟩ s h
      change HasCircuitSize 6 (dual Row15094.f) s at hd
      rwa [funext posted_dual] at hd

theorem relabel_budgets (f : Fn) (p : Equiv.Perm (Fin 6)) (s : ℕ) :
    HasCircuitSize 6 (fun x => f (x ∘ p)) s ↔ HasCircuitSize 6 f s := by
  refine ⟨fun h => ?_, fun h => relabel_size p f s h⟩
  have hr := relabel_size p.symm _ s h
  simpa [Function.comp_def] using hr

theorem exactMinimum (flipped : Bool) (p : Equiv.Perm (Fin 6)) :
    HasCircuitSize 6 (fun x => form flipped (x ∘ p)) 9 ∧
    ∀ s, HasCircuitSize 6 (fun x => form flipped (x ∘ p)) s → 9 ≤ s := by
  obtain ⟨upper, lower, _⟩ := Row15094.exactMinimum
  refine ⟨(relabel_budgets _ p 9).mpr ((base_budgets flipped 9).mpr upper), ?_⟩
  intro s h
  exact lower s ((base_budgets flipped s).mp ((relabel_budgets _ p s).mp h))

def graphCircuit : Circuit :=
  ⟨[⟨.or, [2,3]⟩, ⟨.or, [4,5]⟩, ⟨.or, [6,7]⟩, ⟨.and, [1,8]⟩,
    ⟨.and, [2,3]⟩, ⟨.and, [4,5]⟩, ⟨.or, [10,11]⟩, ⟨.or, [9,12]⟩,
    ⟨.or, [0,13]⟩], 14⟩

set_option maxRecDepth 8192 in
theorem base_witness (flipped : Bool) : ∃ C : Circuit, Monotone2 C ∧ C.size = 9 ∧
    ∀ x, C.eval (List.ofFn x) = form flipped x := by
  cases flipped
  · exact ⟨Row15094.witness, Row15094.witness_correct⟩
  · refine ⟨graphCircuit, ?_, rfl, ?_⟩
    · simp [Monotone2, graphCircuit]
    · decide +kernel

open PEqualNP.Outside.L_meta_12184.Transfer (relabel relGate rel_fold rel_init) in
theorem monotone_witness (flipped : Bool) (p : Equiv.Perm (Fin 6)) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 9 ∧
      ∀ x, C.eval (List.ofFn x) = form flipped (x ∘ p) := by
  obtain ⟨C, hm, hs, he⟩ := base_witness flipped
  refine ⟨relabel 6 6 p C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', mem, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm g' mem).1, by simpa [relGate] using (hm g' mem).2⟩
  · simpa [relabel, Circuit.size] using hs
  · intro x
    rw [← he (x ∘ p)]
    exact (rel_fold 6 6 p C.gates _ _ (rel_init 6 6 p x)).2.2 C.output

/-- Tables use bit r for the output on the row with binary encoding r. -/
def inputWords : List Nat := (List.range 6).map fun i =>
  (List.range 64).foldl (fun w r => if r.testBit i then w ||| 2^r else w) 0

def word (flipped : Bool) (a b c d e f : Nat) : Nat :=
  if flipped then a ||| (b &&& (c ||| d ||| e ||| f)) ||| (c &&& d) ||| (e &&& f)
  else a &&& (b ||| (c &&& d &&& e &&& f)) &&& (c ||| d) &&& (e ||| f)

/-- Choose the independent input, then the central vertex, then one of the
three unordered pairings of the four peripheral vertices. -/
def labeled (flipped : Bool) : List Nat := do
  let a ← inputWords
  let b ← inputWords.erase a
  match (inputWords.erase a).erase b with
  | [c, d, e, f] => [word flipped a b c d e f, word flipped a b c e d f, word flipped a b c f d e]
  | _ => []

set_option maxRecDepth 8192 in
theorem distinct_tables :
    (labeled false).length = 90 ∧ (labeled true).length = 90 ∧
    ((labeled false) ++ (labeled true)).eraseDups.length = 180 := by decide +kernel

end Row15094Butterfly
#print axioms Row15094Butterfly.exactMinimum
