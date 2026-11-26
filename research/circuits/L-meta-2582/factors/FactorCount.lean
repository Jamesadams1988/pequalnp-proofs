import Mathlib

namespace IncidenceReadTwo.FactorCount
open Finset
variable {P L J : Type*} [DecidableEq P] [DecidableEq L] [Fintype L] [Fintype J]

/-- A clause is an OR of raw point and line variables. -/
def Hit (ap : Finset P) (al : Finset L) (s : Finset P) (t : Finset L) : Prop :=
  (∃ p ∈ s, p ∈ ap) ∨ (∃ l ∈ t, l ∈ al)

/-- The largest set of lines avoiding all selected points. -/
def avoids (neighbors : P → Finset L) (s : Finset P) : Finset L :=
  univ \ s.biUnion neighbors

omit [DecidableEq P] in
theorem escaping (neighbors accepted : P → Finset L)
    (sub : ∀ p, accepted p ⊆ neighbors p)
    (linear : ∀ p u, p ≠ u → (neighbors p ∩ neighbors u).card ≤ 1)
    {s : Finset P} {p : P} (out : p ∉ s) (large : s.card < (accepted p).card) :
    ∃ l ∈ accepted p, l ∈ avoids neighbors s := by
  classical
  let bad := s.biUnion (fun u => neighbors p ∩ neighbors u)
  have bound : bad.card ≤ s.card := calc
    _ ≤ ∑ u ∈ s, (neighbors p ∩ neighbors u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ s, 1 := sum_le_sum fun u hu => linear p u (fun e => out (e ▸ hu))
    _ = _ := by simp
  have ns : ¬ accepted p ⊆ bad := fun h => (Nat.not_lt_of_ge ((card_le_card h).trans bound)) large
  obtain ⟨l, hl, hb⟩ := not_subset.mp ns
  refine ⟨l, hl, mem_sdiff.mpr ⟨mem_univ _, ?_⟩⟩
  intro h
  obtain ⟨u, hu, hlu⟩ := mem_biUnion.mp h
  exact hb (mem_biUnion.mpr ⟨u, hu, mem_inter.mpr ⟨sub p hl,hlu⟩⟩)

/-- A safe AND of OR factors must distinguish every small subset of the
    points whose individually accepted incidence degree exceeds r. The
    factors may be shared. No assumption is made about clause lengths. -/
theorem factors (neighbors accepted : P → Finset L) (U : Finset P) (r : ℕ)
    (ap : J → Finset P) (al : J → Finset L)
    (sub : ∀ p, accepted p ⊆ neighbors p)
    (linear : ∀ p u, p ≠ u → (neighbors p ∩ neighbors u).card ≤ 1)
    (degree : ∀ p ∈ U, r < (accepted p).card)
    (accept : ∀ p ∈ U, ∀ l ∈ accepted p, ∀ j, p ∈ ap j ∨ l ∈ al j)
    (safe : ∀ s t, (∀ j, Hit (ap j) (al j) s t) → ∃ p ∈ s, ∃ l ∈ t, l ∈ neighbors p) :
    (U.powerset.filter (fun s => s.card ≤ r)).card ≤ Fintype.card J := by
  classical
  let fam := U.powerset.filter (fun s => s.card ≤ r)
  have miss (s : ↥fam) : ∃ j, ¬ Hit (ap j) (al j) s.val (avoids neighbors s.val) := by
    by_contra! h
    obtain ⟨p,hp,l,hl,hlp⟩ := safe _ _ h
    exact (mem_sdiff.mp hl).2 (mem_biUnion.mpr ⟨p,hp,hlp⟩)
  choose f hf using miss
  have sep (s t : ↥fam) (h : f s = f t) : s.val ⊆ t.val := by
    intro p hp
    by_contra out
    have ps : p ∈ U := (mem_powerset.mp (mem_filter.mp s.property).1) hp
    obtain ⟨l,hl,ht⟩ := escaping neighbors accepted sub linear out
      (lt_of_le_of_lt (mem_filter.mp t.property).2 (degree p ps))
    rcases accept p ps l hl (f s) with ha | ha
    · exact hf s (Or.inl ⟨p,hp,ha⟩)
    · exact hf t (Or.inr ⟨l,ht,h ▸ ha⟩)
  have inj : Function.Injective f := fun {s t} h => Subtype.ext (Subset.antisymm (sep s t h) (sep t s h.symm))
  simpa [fam] using Fintype.card_le_of_injective f inj

/-- Count the empty set, all singletons, and all pairs. -/
theorem upToTwo (U : Finset P) :
    (U.powerset.filter (fun s => s.card ≤ 2)).card = 1 + U.card + U.card.choose 2 := by
  have sets : U.powerset.filter (fun s => s.card ≤ 2) =
      (U.powersetCard 0 ∪ U.powersetCard 1) ∪ U.powersetCard 2 := by
    ext s
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    constructor
    · rintro ⟨sub,le⟩
      have split : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
      rcases split with e | e | e
      · exact Or.inl (Or.inl ⟨sub,e⟩)
      · exact Or.inl (Or.inr ⟨sub,e⟩)
      · exact Or.inr ⟨sub,e⟩
    · rintro ((⟨sub,e⟩ | ⟨sub,e⟩) | ⟨sub,e⟩) <;> exact ⟨sub, by omega⟩
  have disj (a b : ℕ) (ne : a ≠ b) : Disjoint (U.powersetCard a) (U.powersetCard b) := by
    apply disjoint_left.mpr
    intro s ha hb
    exact ne ((mem_powersetCard.mp ha).2.symm.trans (mem_powersetCard.mp hb).2)
  rw [sets,card_union_of_disjoint (disjoint_union_left.mpr ⟨disj 0 2 (by decide),disj 1 2 (by decide)⟩),
    card_union_of_disjoint (disj 0 1 (by decide))]
  simp

/-- On the literal projective-plane incidence relation, a full product of
    OR clauses needs at least one more factor than N(q+2). -/
theorem plane {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2 + q + 1)
    (deg : ∀ l : Fin N, (univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p u : Fin N, p ≠ u → ∃! l, I p l ∧ I u l)
    (ap al : J → Finset (Fin N))
    (accept : ∀ p l : Fin N, I p l → ∀ j, p ∈ ap j ∨ l ∈ al j)
    (safe : ∀ s t, (∀ j, Hit (ap j) (al j) s t) → ∃ p ∈ s, ∃ l ∈ t, I p l) :
    N*(q+2)+1 ≤ Fintype.card J := by
  classical
  let nb (l : Fin N) := univ.filter fun p => I p l
  have linear (l m : Fin N) (hlm : l ≠ m) : (nb l ∩ nb m).card ≤ 1 := by
    rw [card_le_one]
    intro p hp u hu
    by_contra hpu
    obtain ⟨center,_,h⟩ := unique p u hpu
    simp only [nb, mem_inter, mem_filter, mem_univ, true_and] at hp hu
    exact hlm ((h l ⟨hp.1,hu.1⟩).trans (h m ⟨hp.2,hu.2⟩).symm)
  have h := factors nb nb univ 2 al ap (fun _ => Subset.rfl) linear
    (fun l _ => by change 2 < (univ.filter fun p => I p l).card; rw [deg]; omega)
    (fun l _ p hp j => (accept p l (mem_filter.mp hp).2 j).symm)
    (fun t s h => by
      obtain ⟨p,hp,l,hl,inc⟩ := safe s t (fun j => (h j).symm)
      exact ⟨l,hl,p,hp,mem_filter.mpr ⟨mem_univ _,inc⟩⟩)
  rw [upToTwo,card_univ,Fintype.card_fin,Nat.choose_two_right] at h
  have width : 2*(q+1) ≤ N-1 := by
    have hq2 := Nat.mul_le_mul_left q hq
    rw [hN]
    simp only [Nat.add_sub_cancel]
    nlinarith
  have pairs : N*(q+1) ≤ N*(N-1)/2 := (Nat.le_div_iff_mul_le (by decide)).mpr <| by
    calc N*(q+1)*2 = N*(2*(q+1)) := by ring
         _ ≤ N*(N-1) := Nat.mul_le_mul_left _ width
  have total : N*(q+2) = N+N*(q+1) := by ring
  omega

/-- A binary node to expand during a backwards scan of a conjunction DAG. -/
structure Join where
  wire : ℕ
  left : ℕ
  right : ℕ

def expand (g : Join) (pending : Finset ℕ) : Finset ℕ :=
  if g.wire ∈ pending then insert g.left (insert g.right (pending.erase g.wire)) else pending

def frontier (nodes : List Join) (root : ℕ) := nodes.foldl (fun p g => expand g p) {root}

theorem expand_card (g : Join) (p : Finset ℕ) : (expand g p).card ≤ p.card + 1 := by
  unfold expand
  split_ifs with h
  · have one := card_insert_le g.right (p.erase g.wire)
    have two := card_insert_le g.left (insert g.right (p.erase g.wire))
    have erase := card_erase_add_one h
    omega
  · omega

theorem frontier_card (nodes : List Join) (root : ℕ) : (frontier nodes root).card ≤ nodes.length + 1 := by
  have aux (ops : List Join) (p : Finset ℕ) :
      (ops.foldl (fun acc g => expand g acc) p).card ≤ ops.length + p.card := by
    induction ops generalizing p with
    | nil => simp
    | cons g ops ih =>
      simp only [List.foldl_cons,List.length_cons]
      have a := ih (expand g p)
      have b := expand_card g p
      omega
  simpa [frontier] using aux nodes {root}

/-- A product-of-sums block rich on t rows has a private conjunction-gate
    budget sufficient for the row stars of its accepted pairs. OR clauses
    are free in this accounting and the conjunction DAG may have fanout. -/
theorem denseBlock (neighbors accepted : P → Finset L) (U : Finset P) (m : ℕ)
    (nodes : List Join) (root : ℕ) (ap : ℕ → Finset P) (al : ℕ → Finset L)
    (sub : ∀ p, accepted p ⊆ neighbors p)
    (linear : ∀ p u, p ≠ u → (neighbors p ∩ neighbors u).card ≤ 1)
    (minDeg : ∀ p ∈ U, 2 < (accepted p).card)
    (maxDeg : ∀ p ∈ U, (accepted p).card ≤ m)
    (many : 2*m+1 ≤ U.card)
    (accept : ∀ p ∈ U, ∀ l ∈ accepted p, ∀ j ∈ frontier nodes root, p ∈ ap j ∨ l ∈ al j)
    (safe : ∀ s t, (∀ j ∈ frontier nodes root, Hit (ap j) (al j) s t) → ∃ p ∈ s, ∃ l ∈ t, l ∈ neighbors p) :
    (∑ p ∈ U, (accepted p).card) + U.card ≤ nodes.length := by
  classical
  let js := frontier nodes root
  have cut := factors neighbors accepted U 2 (fun j : ↥js => ap j) (fun j : ↥js => al j)
    sub linear minDeg (fun p hp l hl j => accept p hp l hl j j.property)
    (fun s t h => safe s t (fun j hj => h ⟨j,hj⟩))
  rw [upToTwo, Fintype.card_coe, Nat.choose_two_right] at cut
  have upper : js.card ≤ nodes.length + 1 := frontier_card nodes root
  have hsum : (∑ p ∈ U, (accepted p).card) ≤ U.card*m := by
    simpa using sum_le_sum maxDeg
  have width : 2*m ≤ U.card-1 := by omega
  have pairs : U.card*m ≤ U.card*(U.card-1)/2 := (Nat.le_div_iff_mul_le (by decide)).mpr <| by
    calc U.card*m*2 = U.card*(2*m) := by ring
         _ ≤ U.card*(U.card-1) := Nat.mul_le_mul_left _ width
  omega

/-- Evaluate a list of binary conjunctions, with the last gate listed first. -/
def run : List Join → (ℕ → Prop) → ℕ → Prop
  | [], v => v
  | g :: ops, v => fun w => if w = g.wire then run ops v g.left ∧ run ops v g.right else run ops v w

private theorem expand_iff (g : Join) (p : Finset ℕ) (v : ℕ → Prop) :
    (∀ i ∈ p, if i = g.wire then v g.left ∧ v g.right else v i) ↔ ∀ i ∈ expand g p, v i := by
  classical
  by_cases hg : g.wire ∈ p
  · constructor
    · intro h i hi
      have both : v g.left ∧ v g.right := by simpa using h g.wire hg
      simp only [expand,hg,ite_true,mem_insert,mem_erase] at hi
      rcases hi with rfl | rfl | ⟨ne,hm⟩
      · exact both.1
      · exact both.2
      · simpa [ne] using h i hm
    · intro h i hi
      by_cases hwire : i = g.wire
      · simp only [hwire,ite_true]
        exact ⟨h _ (by simp [expand,hg]),h _ (by simp [expand,hg])⟩
      · simp only [hwire,ite_false]
        exact h i (by simp [expand,hg,hi,hwire])
  · simp only [expand,hg,ite_false]
    constructor <;> intro h i hi <;> have ne : i ≠ g.wire := fun e => hg (e ▸ hi)
    · simpa [ne] using h i hi
    · simpa [ne] using h i hi

/-- Backwards expansion preserves the meaning of a binary AND block. This
    permits arbitrary reuse of intermediate conjunctions and frontier wires. -/
theorem run_frontier (nodes : List Join) (v : ℕ → Prop) (root : ℕ) :
    run nodes v root ↔ ∀ i ∈ frontier nodes root, v i := by
  have allw (ops : List Join) (p : Finset ℕ) :
      (∀ i ∈ p, run ops v i) ↔ ∀ i ∈ ops.foldl (fun acc g => expand g acc) p, v i := by
    induction ops generalizing p with
    | nil => rfl
    | cons g ops ih =>
      simp only [run,List.foldl_cons]
      exact (expand_iff g p (run ops v)).trans (ih (expand g p))
  simpa [frontier] using allw nodes {root}

omit [DecidableEq P] [DecidableEq L] [Fintype L] in
/-- Replacing one disjunct by its accepted incidence pairs preserves the
    entire incidence function, even if this loses some larger true inputs
    of that disjunct. The other disjunct only has to be monotone. -/
theorem replaceAtTop (neighbors accepted : P → Finset L)
    (old rest : Finset P → Finset L → Prop)
    (exactOld : ∀ s t, rest s t ∨ old s t ↔ ∃ p ∈ s, ∃ l ∈ t, l ∈ neighbors p)
    (monoRest : ∀ s t s' t', s ⊆ s' → t ⊆ t' → rest s t → rest s' t')
    (atPairs : ∀ p l, old {p} {l} → l ∈ accepted p)
    (sub : ∀ p, accepted p ⊆ neighbors p) (s : Finset P) (t : Finset L) :
    (rest s t ∨ ∃ p ∈ s, ∃ l ∈ t, l ∈ accepted p) ↔ ∃ p ∈ s, ∃ l ∈ t, l ∈ neighbors p := by
  constructor
  · rintro (h | ⟨p,hp,l,hl,he⟩)
    · exact (exactOld s t).mp (Or.inl h)
    · exact ⟨p,hp,l,hl,sub p he⟩
  · rintro ⟨p,hp,l,hl,he⟩
    have single := (exactOld {p} {l}).mpr ⟨p,mem_singleton_self _,l,mem_singleton_self _,he⟩
    rcases single with prev | localHit
    · exact Or.inl (monoRest _ _ _ _ (singleton_subset_iff.mpr hp) (singleton_subset_iff.mpr hl) prev)
    · exact Or.inr ⟨p,hp,l,hl,atPairs p l localHit⟩

end IncidenceReadTwo.FactorCount
#print axioms IncidenceReadTwo.FactorCount.factors

#print axioms IncidenceReadTwo.FactorCount.plane

#print axioms IncidenceReadTwo.FactorCount.denseBlock

#print axioms IncidenceReadTwo.FactorCount.replaceAtTop

#print axioms IncidenceReadTwo.FactorCount.run_frontier
