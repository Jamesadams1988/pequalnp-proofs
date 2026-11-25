import PEqualNP.Defs

/-! A row-specific obstruction to a single filtered rectangle whose remaining
edges are covered by direct stars. Point and line coordinates run from 0 to 19;
in the posted 40-input formula, the physical line index has offset 20. -/
namespace Row9802.Filter
abbrev V := Fin 20
def listed : List (ℕ × ℕ) := [
  (0,20), (0,25), (0,27), (0,37), (1,21), (1,26), (1,28), (1,38), (2,21), (2,22), (2,27), (2,29), (2,39), (3,20), (3,22), (3,23), (3,28), (3,30), (4,23), (4,24), (4,29), (4,31), (5,21), (5,24), (5,25), (5,30), (5,32), (6,22), (6,25), (6,26), (6,31), (6,33), (7,23), (7,26), (7,27), (7,32), (7,34), (8,24), (8,27), (8,28), (8,33), (8,35), (9,25), (9,28), (9,29), (9,34), (9,36), (10,26), (10,29), (10,30), (10,35), (10,37), (11,27), (11,30), (11,31), (11,36), (11,38), (12,28), (12,31), (12,32), (12,37), (12,39), (13,20), (13,29), (13,32), (13,33), (13,38), (14,30), (14,33), (14,34), (14,39), (15,20), (15,21), (15,31), (15,34), (15,35), (16,22), (16,32), (16,35), (16,36), (17,21), (17,23), (17,33), (17,36), (17,37), (18,22), (18,24), (18,34), (18,37), (18,38), (19,23), (19,25), (19,35), (19,38), (19,39)]
def mask : V → BitVec 20 := ![131233,262466,524934,1293,2584,5170,10340,20680,41360,82720,165440,330880,661760,274945,549888,51203,102404,204810,409620,819240]
def edge (p l : V) : Prop := (mask p).getLsbD l.val = true
instance (p l : V) : Decidable (edge p l) := by unfold edge; infer_instance

theorem listedAgrees : ∀ p l : V, ((p.val,l.val+20) ∈ listed) ↔ edge p l := by
  intro i
  fin_cases i <;> decide +kernel

def matching : Fin 5 → V → V := ![
  ![5,6,9,8,11,10,2,7,15,14,17,16,19,18,13,0,12,1,4,3],
  ![0,1,19,2,9,4,6,3,7,8,15,18,17,12,10,11,16,13,14,5],
  ![0,18,7,3,4,1,13,12,8,5,6,10,11,9,19,14,2,16,17,15],
  ![7,6,1,0,3,12,5,14,4,9,10,11,8,13,19,15,16,17,2,18],
  ![17,8,2,10,4,5,11,6,13,16,9,7,12,0,14,1,15,3,18,19]]

/-- The listed table has no four-cycle. -/
private def common (p q : V) := Finset.univ.filter (fun l => edge p l ∧ edge q l)

set_option maxHeartbeats 0 in
private theorem commonSmall : ∀ p q : V, p ≠ q → (common p q).card ≤ 1 := by
  intro i
  fin_cases i <;> decide +kernel

theorem thin : ∀ (p q l m : V), edge p l → edge p m → edge q l → edge q m → p = q ∨ l = m := by
  intro p q l m hpl hpm hql hqm
  by_cases eq : p = q
  · exact .inl eq
  · exact .inr (Finset.card_le_one.mp (commonSmall p q eq) l
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,hql⟩) m
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpm,hqm⟩))

theorem coversEdges : ∀ p l, edge p l → ∃ k, matching k p = l := by
  intro i
  fin_cases i <;> decide +kernel
theorem matchesEdges : ∀ k p, edge p (matching k p) := by
  intro i
  fin_cases i <;> decide +kernel
theorem injectiveMatching : ∀ k, Function.Injective (matching k) := by
  intro i
  fin_cases i <;> decide +kernel

/-- On a two-active input, the filtered rectangle accepts precisely a pair
inside A × B on which at least one endpoint belongs to the marking disjunction. -/
theorem markedPair (a b markPoint markLine : Bool) :
    ((a && b) && (markPoint || markLine)) =
      ((a && markPoint && b) || (a && b && markLine)) := by
  cases a <;> cases b <;> cases markPoint <;> cases markLine <;> decide

/-- When the only marks within A and B are the two centers, the filtered
rectangle equals the union of their stars on every input, including triples. -/
theorem doubleStar (u v morePoints moreLines : Bool) :
    (((u || morePoints) && (v || moreLines)) && (u || v)) =
      ((u && (v || moreLines)) || ((u || morePoints) && v)) := by
  cases u <;> cases v <;> cases morePoints <;> cases moreLines <;> decide

/-- Two marked points in A force B to have at most one distinct member. -/
theorem onlyOneMarkedPoint {A B D : Finset V}
    (sound : ∀ p ∈ A, p ∈ D → ∀ l ∈ B, edge p l)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (du : u ∈ D) (dv : v ∈ D) (ne : u ≠ v) :
    ∀ i ∈ B, ∀ j ∈ B, i = j := by
  intro i hi j hj
  exact (thin u v i j (sound _ hu du _ hi) (sound _ hu du _ hj)
    (sound _ hv dv _ hi) (sound _ hv dv _ hj)).resolve_left ne

theorem onlyOneMarkedLine {A B D : Finset V}
    (sound : ∀ l ∈ B, l ∈ D → ∀ p ∈ A, edge p l)
    {u v : V} (hu : u ∈ B) (hv : v ∈ B) (du : u ∈ D) (dv : v ∈ D) (ne : u ≠ v) :
    ∀ i ∈ A, ∀ j ∈ A, i = j := by
  intro i hi j hj
  exact (thin i j u v (sound _ hu du _ hi) (sound _ hv dv _ hi)
    (sound _ hu du _ hj) (sound _ hv dv _ hj)).resolve_right ne

/-- The edge pairs retained by the double-star filter. The central edge
is counted on the point side and excluded from the line side. -/
def doublePairs (u v : V) (A B : Finset V) : Finset (V × V) :=
  (B.image (fun l => (u,l))) ∪ ((A.erase u).image (fun p => (p,v)))

theorem doublePairsCard (u v : V) (A B : Finset V) (hu : u ∈ A) (hv : v ∈ B) :
    (doublePairs u v A B).card = (A.card-1) + (B.card-1) + 1 := by
  have dis : Disjoint (B.image (fun l => (u,l))) ((A.erase u).image (fun p => (p,v))) := by
    refine Finset.disjoint_left.mpr ?_
    intro e he hf
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p,hp,pair⟩ := Finset.mem_image.mp hf
    exact (Finset.mem_erase.mp hp).1 (congrArg Prod.fst pair)
  rw [doublePairs,Finset.card_union_of_disjoint dis,
    Finset.card_image_of_injective _ (fun x y he => congrArg Prod.snd he),
    Finset.card_image_of_injective _ (fun x y he => congrArg Prod.fst he),
    Finset.card_erase_of_mem hu]
  have pos : 0 < B.card := Finset.card_pos.mpr ⟨v,hv⟩
  omega

/-- Every direct-star cover of the edges outside an adjacent point/line pair
has at least nineteen centers. A perfect matching containing that edge leaves
nineteen disjoint edges that avoid both centers. -/
theorem residualCenters (u v : V) (uv : edge u v) (P L : Finset V)
    (covers : ∀ p l, edge p l → p ≠ u → l ≠ v → p ∈ P ∨ l ∈ L) :
    19 ≤ P.card + L.card := by
  obtain ⟨k, hk⟩ := coversEdges u v uv
  let M := matching k
  let missed := (Finset.univ.erase u) \ P
  have inj : Function.Injective M := injectiveMatching k
  have inc : missed.image M ⊆ L := by
    intro l hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨inRest,np⟩ := Finset.mem_sdiff.mp hp
    have nu := (Finset.mem_erase.mp inRest).1
    have nv : M p ≠ v := fun h => nu (inj (h.trans hk.symm))
    exact (covers p (M p) (matchesEdges k p) nu nv).resolve_left np
  have cap := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ inj] at cap
  have all : Finset.univ.erase u ⊆ P ∪ missed := by
    intro p h
    exact Finset.mem_union.mpr (by by_cases hp : p ∈ P <;> simp_all [missed])
  have sz := (Finset.card_le_card all).trans (Finset.card_union_le P missed)
  have known : (Finset.univ.erase u).card = 19 := by simp
  omega

/-- If building the grouped rectangle costs at least as many gates as pairs
it covers, and the other edges use direct stars, the 113-gate budget fails. -/
theorem filteredCost (u v : V) (uv : edge u v) (P L : Finset V)
    (covers : ∀ p l, edge p l → p ≠ u → l ≠ v → p ∈ P ∨ l ∈ L)
    (covered rest rectangleCost : ℕ) (total : covered + rest = 95)
    (cost : covered ≤ rectangleCost) : 114 ≤ rectangleCost + rest + P.card + L.card := by
  have h := residualCenters u v uv P L covers
  omega

end Row9802.Filter
#print axioms Row9802.Filter.thin
#print axioms Row9802.Filter.filteredCost
