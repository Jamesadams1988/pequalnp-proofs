import PEqualNP.MetaComplexity.Helpers.ReadTwoBridge

/-! Pointwise coarsening of the official capped read-vector tables. -/
namespace IncidenceReadTwo.Monotonicity
open PEqualNP.ReadK PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.ReadTwoBridge

abbrev Vectors := List (List ℕ)

def coarsen (k : ℕ) (v : List ℕ) := v.map (fun a => min a (k+1))

/-- Equality after coarsening, up to the order and deduplication of vectors. -/
def Related (k : ℕ) (small large : Vectors) : Prop :=
  ∀ v, v ∈ small ↔ ∃ w ∈ large, coarsen k w = v

private theorem coarsen_add {k K : ℕ} (le : k ≤ K) (a b : List ℕ) :
    coarsen k (capAdd K a b) = capAdd k (coarsen k a) (coarsen k b) := by
  induction a generalizing b with
  | nil => simp [coarsen,capAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [coarsen,capAdd]
    | cons y ys =>
      change min (min (x+y) (K+1)) (k+1) :: coarsen k (capAdd K xs ys) =
        min (min x (k+1) + min y (k+1)) (k+1) :: capAdd k (coarsen k xs) (coarsen k ys)
      rw [ih ys]
      congr 1; omega

private theorem related_empty (k : ℕ) : Related k [] [] := by simp [Related]

private theorem related_single {k : ℕ} {v w : List ℕ} (eq : coarsen k w = v) :
    Related k [v] [w] := by simp [Related,eq,eq_comm]

private theorem related_or {k : ℕ} {a A b B : Vectors} (ha : Related k a A) (hb : Related k b B) :
    Related k (b.foldl insertNew a) (B.foldl insertNew A) := by
  intro v
  rw [mem_foldl_insertNew,ha v,hb v]
  constructor
  · rintro (⟨w,hw,e⟩ | ⟨w,hw,e⟩)
    · exact ⟨w,(mem_foldl_insertNew B A w).mpr (Or.inl hw),e⟩
    · exact ⟨w,(mem_foldl_insertNew B A w).mpr (Or.inr hw),e⟩
  · rintro ⟨w,hw,e⟩
    rcases (mem_foldl_insertNew B A w).mp hw with old | new
    · exact Or.inl ⟨w,old,e⟩
    · exact Or.inr ⟨w,new,e⟩

private theorem related_and {k K : ℕ} (le : k ≤ K) {a A b B : Vectors}
    (ha : Related k a A) (hb : Related k b B) : Related k (andStep k a b) (andStep K A B) := by
  intro v
  rw [mem_andStep]
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    obtain ⟨X,hX,rfl⟩ := (ha x).mp hx
    obtain ⟨Y,hY,rfl⟩ := (hb y).mp hy
    exact ⟨capAdd K X Y,(mem_andStep K A B _).mpr ⟨X,hX,Y,hY,rfl⟩,coarsen_add le X Y⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨X,hX,Y,hY,rfl⟩ := (mem_andStep K A B w).mp hw
    exact ⟨_,(ha _).mpr ⟨X,hX,rfl⟩,_,(hb _).mpr ⟨Y,hY,rfl⟩,coarsen_add le X Y⟩

private theorem related_leaf (k K : ℕ) (S : List ℕ) (i : ℕ) :
    Related k (leafVectors S k i) (leafVectors S K i) := by
  by_cases hi : i ∈ S
  · simp only [leafVectors,hi,ite_true]
    apply related_single
    clear hi
    induction S with
    | nil => rfl
    | cons x xs ih =>
      change min (if x = i then min 1 (K+1) else 0) (k+1) :: _ = (if x = i then min 1 (k+1) else 0) :: _
      congr 1
      · split <;> omega
  · simpa [leafVectors,hi] using related_empty k

private theorem coarsen_zero (k : ℕ) (S : List ℕ) : coarsen k (S.map fun _ => 0) = S.map fun _ => 0 := by
  simp [coarsen]

private theorem fold_related {α β : Type*} {r : α → α → Prop} {t : β → β → Prop}
    {f g : β → α → β} (step : ∀ ⦃a A b B⦄, t a A → r b B → t (f a b) (g A B))
    {xs ys : List α} (h : List.Forall₂ r xs ys) {z Z : β} (init : t z Z) :
    t (xs.foldl f z) (ys.foldl g Z) := by
  induction h generalizing z Z with
  | nil => exact init
  | cons head _ ih => exact ih (step init head)

private theorem map_related {α β : Type*} {r : β → β → Prop} (xs : List α) (f g : α → β)
    (h : ∀ x, r (f x) (g x)) : List.Forall₂ r (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x) ih

private theorem get_related {k : ℕ} {a A : List Vectors} (h : List.Forall₂ (Related k) a A) (i : ℕ) :
    Related k (a.getD i []) (A.getD i []) := by
  induction h generalizing i with
  | nil => simpa using related_empty k
  | cons head _ ih => cases i with
    | zero => exact head
    | succ j => exact ih j

private theorem gate_related {k K : ℕ} (le : k ≤ K) (S : List ℕ) (g : Gate)
    {xs ys : List Vectors} (h : List.Forall₂ (Related k) xs ys) :
    Related k (rvG S k xs g) (rvG S K ys g) := by
  cases op : g.op <;> simp only [rvG,op]
  · exact fold_related (r := Related k) (t := Related k) (f := andStep k) (g := andStep K)
      (fun {_ _ _ _} ha hb => related_and le ha hb) h (related_single (coarsen_zero k S))
  · exact fold_related (r := Related k) (t := Related k) (f := fun acc A => A.foldl insertNew acc)
      (g := fun acc A => A.foldl insertNew acc) (fun {_ _ _ _} ha hb => related_or ha hb) h (related_empty k)
  all_goals exact related_empty k

/-- Every smaller-cap table, at every wire, is exactly the coarsening of the larger-cap table. -/
theorem vectors {k K : ℕ} (le : k ≤ K) (C : Circuit) (n : ℕ) (S : List ℕ) (i : ℕ) :
    Related k ((readVectors C n S k).getD i []) ((readVectors C n S K).getD i []) := by
  rw [rv_eq,rv_eq]
  apply get_related
  have step (a A : List Vectors) (h : List.Forall₂ (Related k) a A) (g : Gate) :
      List.Forall₂ (Related k) (a ++ [rvG S k (g.inputs.map fun i => a.getD i []) g])
        (A ++ [rvG S K (g.inputs.map fun i => A.getD i []) g]) := by
    exact List.rel_append h (.cons (gate_related le S g (map_related _ _ _ (get_related h))) .nil)
  have eqg : List.Forall₂ Eq C.gates C.gates := by
    simp
  exact fold_related (r := Eq) (fun {a A g G} h eq => eq ▸ step a A h g)
    eqg
    (map_related _ _ _ (related_leaf k K S))

private theorem coarsen_fixed {k : ℕ} (v : List ℕ) (h : ∀ a ∈ v, a ≤ k) : coarsen k v = v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have ha := h a (by simp)
    have hv : ∀ b ∈ v, b ≤ k := fun b hb => h b (by simp [hb])
    change min a (k+1) :: coarsen k v = a :: v
    rw [min_eq_left (by omega), ih hv]

/-- Feasible vectors agree literally in both tables, even when order or
    deduplication differs. One table at cap K tests all smaller bounds. -/
theorem feasibleVector {k K : ℕ} (le : k ≤ K) (C : Circuit) (n : ℕ) (S : List ℕ) (i : ℕ)
    (v : List ℕ) (ok : ∀ a ∈ v, a ≤ k) :
    v ∈ (readVectors C n S k).getD i [] ↔ v ∈ (readVectors C n S K).getD i [] := by
  have h := vectors le C n S i v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := h.mp hv
    have good : ∀ a ∈ w, a ≤ k := by
      intro a ha
      have mem : min a (k+1) ∈ coarsen k w := List.mem_map.mpr ⟨a,ha,rfl⟩
      have cap := ok _ mem
      omega
    simpa [coarsen_fixed w good] using hw
  · exact fun hv => h.mpr ⟨v,hv,coarsen_fixed v ok⟩

/-- A feasible small-cap vector is preserved at every larger read bound. -/
theorem readsAtMost_mono {k K : ℕ} (le : k ≤ K) (C : Circuit) (n : ℕ) (S : List ℕ)
    (h : readsAtMost C n S k = true) : readsAtMost C n S K = true := by
  obtain ⟨v,hv,ok⟩ := List.any_eq_true.mp h
  have bound : ∀ a ∈ v, a ≤ k := fun a ha => of_decide_eq_true (List.all_eq_true.mp ok a ha)
  exact List.any_eq_true.mpr ⟨v,(feasibleVector le C n S _ v bound).mp hv,
    List.all_eq_true.mpr (fun a ha => decide_eq_true ((bound a ha).trans le))⟩

theorem isReadK_mono {k K n : ℕ} (le : k ≤ K) (C : Circuit) (h : IsReadK n C k) : IsReadK n C K :=
  fun S prime => readsAtMost_mono le C n (setList S) (h S prime)

end IncidenceReadTwo.Monotonicity
#print axioms IncidenceReadTwo.Monotonicity.vectors
#print axioms IncidenceReadTwo.Monotonicity.isReadK_mono
