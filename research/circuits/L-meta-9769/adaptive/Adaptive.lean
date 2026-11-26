import PEqualNP.MetaComplexity.Helpers.ForestBound

namespace ProjectiveEdge.Adaptive
open Finset PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.Forest
variable {n : ℕ}
abbrev V (n : ℕ) := Fin (n+1)

/-- The residual graph on the original input wires. -/
def induced (G : SimpleGraph (V n)) (S : Finset (V n)) : SimpleGraph (V n) where
  Adj i j := i ∈ S ∧ j ∈ S ∧ G.Adj i j
  symm := ⟨fun _ _ ⟨hi,hj,e⟩ => ⟨hj,hi,e.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.2.2⟩

def Live (G : SimpleGraph (V n)) (S : Finset (V n)) := ∀ i ∈ S, ∃ j ∈ S, G.Adj i j

/-- Uniformity in the unit set permits a DAG of certificates keyed only by
    the residual subgraph and the required budget beyond the unit count. -/
def Bound (G : SimpleGraph (V n)) (S : Finset (V n)) (k : ℕ) :=
  ∀ U : Finset (V n), Disjoint U S → ∀ s, HasCircuitSize (n+1) (F (induced G S) U) s → U.card+k ≤ s

theorem leaf {G : SimpleGraph (V n)} {S : Finset (V n)} {k : ℕ} (live : Live G S)
    (count : k+1 ≤ S.card) : Bound G S k := by
  intro U dis s hs
  have bound := dep_lower_set _ (F (induced G S) U) (U ∪ S) (fun i hi => by
    rcases mem_union.mp hi with memU|memS
    · exact F_dep_A _ _ _ memU
    · obtain ⟨j,hj,ij⟩ := live i memS
      exact F_dep _ _ i j ⟨memS,hj,ij⟩ (fun h => disjoint_left.mp dis h hj)) s hs
  rw [card_union_of_disjoint dis] at bound
  omega

def neighbors (G : SimpleGraph (V n)) [DecidableRel G.Adj] (S : Finset (V n)) (p : V n) :=
  S.filter (G.Adj p)

def prune (G : SimpleGraph (V n)) [DecidableRel G.Adj] (S : Finset (V n)) :=
  S.filter (fun i => ∃ j ∈ S, G.Adj i j)

theorem prune_eq (G : SimpleGraph (V n)) [DecidableRel G.Adj] (S : Finset (V n)) :
    induced G (prune G S) = induced G S := by
  ext i j
  change (i ∈ prune G S ∧ j ∈ prune G S ∧ G.Adj i j) ↔ i ∈ S ∧ j ∈ S ∧ G.Adj i j
  simp only [prune,mem_filter]
  constructor
  · rintro ⟨⟨hi,_⟩,⟨hj,_⟩,h⟩; exact ⟨hi,hj,h⟩
  · rintro ⟨hi,hj,h⟩; exact ⟨⟨hi,j,hj,h⟩,⟨hj,i,hi,h.symm⟩,h⟩

theorem zero_cofactor (G : SimpleGraph (V n)) (S U : Finset (V n)) (p : V n) (pU : p ∉ U) :
    (fun x => F (induced G S) U (Function.update x p false)) = F (induced G (S.erase p)) U := by
  funext x
  apply F_eq
  apply or_congr
  · constructor <;> rintro ⟨i,hi,h⟩ <;> refine ⟨i,hi,?_⟩
    all_goals simpa [Function.update_of_ne (show i ≠ p from fun e => pU (e ▸ hi))] using h
  · constructor
    · rintro ⟨i,j,⟨hi,hj,e⟩,ai,aj⟩
      have ni : i ≠ p := by rintro rfl; simp at ai
      have nj : j ≠ p := by rintro rfl; simp at aj
      exact ⟨i,j,⟨mem_erase.mpr ⟨ni,hi⟩,mem_erase.mpr ⟨nj,hj⟩,e⟩,by simpa [Function.update_of_ne ni] using ai,by simpa [Function.update_of_ne nj] using aj⟩
    · rintro ⟨i,j,⟨hi,hj,e⟩,ai,aj⟩
      exact ⟨i,j,⟨(mem_erase.mp hi).2,(mem_erase.mp hj).2,e⟩,by simpa [Function.update_of_ne (mem_erase.mp hi).1] using ai,by simpa [Function.update_of_ne (mem_erase.mp hj).1] using aj⟩

theorem one_cofactor (G : SimpleGraph (V n)) [DecidableRel G.Adj] (S U : Finset (V n)) (p : V n)
    (hp : p ∈ S) (pU : p ∉ U) :
    (fun x => F (induced G S) U (Function.update x p true)) =
      F (induced G ((S.erase p) \ neighbors G S p)) (U ∪ neighbors G S p) := by
  funext x
  apply F_eq
  constructor
  · rintro (⟨i,hi,h⟩ | ⟨i,j,⟨hi,hj,e⟩,ai,aj⟩)
    · exact Or.inl ⟨i,mem_union_left _ hi,by simpa [Function.update_of_ne (show i ≠ p from fun eq => pU (eq ▸ hi))] using h⟩
    · by_cases ip : i = p
      · subst i
        exact Or.inl ⟨j,mem_union_right _ (mem_filter.mpr ⟨hj,e⟩),by simpa [Function.update_of_ne e.ne.symm] using aj⟩
      by_cases jp : j = p
      · subst j
        exact Or.inl ⟨i,mem_union_right _ (mem_filter.mpr ⟨hi,e.symm⟩),by simpa [Function.update_of_ne ip] using ai⟩
      rw [Function.update_of_ne ip] at ai
      rw [Function.update_of_ne jp] at aj
      by_cases ni : i ∈ neighbors G S p
      · exact Or.inl ⟨i,mem_union_right _ ni,ai⟩
      by_cases nj : j ∈ neighbors G S p
      · exact Or.inl ⟨j,mem_union_right _ nj,aj⟩
      exact Or.inr ⟨i,j,⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨ip,hi⟩,ni⟩,mem_sdiff.mpr ⟨mem_erase.mpr ⟨jp,hj⟩,nj⟩,e⟩,ai,aj⟩
  · rintro (⟨i,hi,xi⟩ | ⟨i,j,⟨hi,hj,e⟩,xi,xj⟩)
    · rcases mem_union.mp hi with ui|ni
      · exact Or.inl ⟨i,ui,by simpa [Function.update_of_ne (show i ≠ p from fun eq => pU (eq ▸ ui))] using xi⟩
      obtain ⟨is,pi⟩ := mem_filter.mp ni
      exact Or.inr ⟨p,i,⟨hp,is,pi⟩,by simp,by simpa [Function.update_of_ne pi.ne.symm] using xi⟩
    · obtain ⟨ip,is⟩ := mem_erase.mp (mem_sdiff.mp hi).1
      obtain ⟨jp,js⟩ := mem_erase.mp (mem_sdiff.mp hj).1
      exact Or.inr ⟨i,j,⟨is,js,e⟩,by simpa [Function.update_of_ne ip] using xi,by simpa [Function.update_of_ne jp] using xj⟩

/-- A single adaptive split. Each child may choose a different vertex next. -/
theorem branch {G : SimpleGraph (V n)} [DecidableRel G.Adj] {S Z O N : Finset (V n)}
    {v : V n} {k kZ kO : ℕ} (hp : v ∈ S) (pv : ∃ w ∈ S, G.Adj v w)
    (hn : N = neighbors G S v) (hz : Z = prune G (S.erase v))
    (ho : O = prune G ((S.erase v) \ N))
    (zedge : ∃ i ∈ Z, ∃ j ∈ Z, G.Adj i j) (oedge : ∃ i ∈ O, ∃ j ∈ O, G.Adj i j)
    (zbound : k ≤ kZ+2) (obound : k ≤ kO+2+N.card)
    (zchild : Bound G Z kZ) (ochild : Bound G O kO) : Bound G S k := by
  intro U dis s hs
  have pU : v ∉ U := fun h => disjoint_left.mp dis h hp
  have geZ : induced G Z = induced G (S.erase v) := hz ▸ prune_eq G _
  have geO : induced G O = induced G ((S.erase v) \ N) := ho ▸ prune_eq G _
  have zero := zero_cofactor G S U v pU
  rw [←geZ] at zero
  have one := one_cofactor G S U v hp pU
  rw [←hn,←geO] at one
  have dU : Disjoint U N := disjoint_left.mpr fun i hi hN => disjoint_left.mp dis hi (mem_filter.mp (hn ▸ hN)).1
  obtain ⟨w,hw,adj⟩ := pv
  have rootDep := F_dep (induced G S) U v w ⟨hp,hw,adj⟩ (fun h => disjoint_left.mp dis h hw)
  have nc (b : Bool) : ∃ x y, F (induced G S) U (Function.update x v b) ≠ F (induced G S) U (Function.update y v b) := by
    cases b with
    | false =>
      obtain ⟨i,hi,j,hj,h⟩ := zedge
      obtain ⟨x,y,hxy⟩ := F_nc (induced G Z) U (Or.inr ⟨i,j,hi,hj,h⟩)
      exact ⟨x,y,(congrFun zero x).trans_ne (hxy.trans_eq (congrFun zero y).symm)⟩
    | true =>
      obtain ⟨i,hi,j,hj,h⟩ := oedge
      obtain ⟨x,y,hxy⟩ := F_nc (induced G O) (U ∪ N) (Or.inr ⟨i,j,hi,hj,h⟩)
      exact ⟨x,y,(congrFun one x).trans_ne (hxy.trans_eq (congrFun one y).symm)⟩
  obtain ⟨b,s',save,hs'⟩ := gate_elim_at n _ v s rootDep nc hs
  cases b with
  | false =>
    rw [zero] at hs'
    have dz : Disjoint U Z := disjoint_left.mpr fun i hi hz' =>
      disjoint_left.mp dis hi ((mem_erase.mp (mem_filter.mp (hz ▸ hz')).1).2)
    have lower := zchild U dz s' hs'
    omega
  | true =>
    rw [one] at hs'
    have ds : Disjoint (U ∪ N) O := by
      apply disjoint_left.mpr
      intro i hi hO
      have rem := (mem_sdiff.mp (mem_filter.mp (ho ▸ hO)).1)
      rcases mem_union.mp hi with u|p
      · exact disjoint_left.mp dis u (mem_erase.mp rem.1).2
      · exact rem.2 p
    have lower := ochild (U ∪ N) ds s' hs'
    rw [card_union_of_disjoint dU] at lower
    omega
end ProjectiveEdge.Adaptive
#print axioms ProjectiveEdge.Adaptive.branch
