import PEqualNP.Defs

/- James Adams. Characterize the exact supports to test for semantic
   read-k on a bipartite incidence function. -/
namespace IncidenceRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

abbrev Vertex (n : ℕ) := Fin (n+n)

def edge {n : ℕ} (p l : Fin n) : Finset (Vertex n) :=
  {Fin.castAdd n p, Fin.natAdd n l}

private theorem left_right {n : ℕ} (p l : Fin n) :
    Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have h' := congrArg Fin.val h
  change p.val = n + l.val at h'
  omega

private theorem left_mem {n : ℕ} (p l a : Fin n) :
    Fin.castAdd n a ∈ edge p l ↔ a = p := by
  simp only [edge, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Fin.ext (congrArg (fun v : Vertex n => v.val) h)
    · exact (left_right a l h).elim
  · rintro rfl
    exact Or.inl rfl

private theorem right_mem {n : ℕ} (p l b : Fin n) :
    Fin.natAdd n b ∈ edge p l ↔ b = l := by
  simp only [edge, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (left_right p b h.symm).elim
    · apply Fin.ext
      have hh := congrArg Fin.val h
      change n + b.val = n + l.val at hh
      omega
  · rintro rfl
    exact Or.inr rfl

private theorem edge_sub {n : ℕ} {p l : Fin n} {S : Finset (Vertex n)}
    (hp : Fin.castAdd n p ∈ S) (hl : Fin.natAdd n l ∈ S) : edge p l ⊆ S := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | h
  · exact hp
  · have e := Finset.mem_singleton.mp h
    simpa only [e] using hl

def Computes {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit) :=
  ∀ z : Vertex n → Bool, circuitFun (n+n) C z =
    decide (∃ p l : Fin n, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true)

private theorem supported {n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {C : Circuit} (h : Computes I C) (S : Finset (Vertex n)) :
    circuitFun (n+n) C (setInput S) = true ↔
      ∃ p l : Fin n, I p l ∧ Fin.castAdd n p ∈ S ∧ Fin.natAdd n l ∈ S := by
  rw [h]
  simp [setInput]

theorem prime_iff_edge {n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {C : Circuit} (h : Computes I C) (S : Finset (Vertex n)) :
    IsPrimeImplicant (n+n) C S ↔ ∃ p l : Fin n, I p l ∧ S = edge p l := by
  constructor
  · rintro ⟨hs, minimal⟩
    obtain ⟨p,l,inc,hp,hl⟩ := (supported h S).mp hs
    refine ⟨p,l,inc,?_⟩
    by_contra ne
    have sub : edge p l ⊆ S := edge_sub hp hl
    have lt : edge p l ⊂ S := lt_of_le_of_ne sub (Ne.symm ne)
    have fals := minimal _ (Finset.mem_ssubsets.mpr lt)
    have tru := (supported h _).mpr ⟨p,l,inc,(left_mem p l p).mpr rfl,(right_mem p l l).mpr rfl⟩
    simp [fals] at tru
  · rintro ⟨p,l,inc,rfl⟩
    refine ⟨(supported h _).mpr ⟨p,l,inc,(left_mem p l p).mpr rfl,(right_mem p l l).mpr rfl⟩,?_⟩
    intro T ht
    have lt := Finset.mem_ssubsets.mp ht
    cases eq : circuitFun (n+n) C (setInput T) with
    | false => rfl
    | true =>
      obtain ⟨a,b,_,ha,hb⟩ := (supported h T).mp eq
      have sub : T ⊆ edge p l := le_of_lt lt
      have e₁ := (left_mem p l a).mp (sub ha)
      have e₂ := (right_mem p l b).mp (sub hb)
      subst a
      subst b
      exact (not_le_of_gt lt (edge_sub ha hb)).elim

theorem read_iff_edges {n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {C : Circuit} (h : Computes I C) (k : ℕ) :
    IsReadK (n+n) C k ↔ ∀ p l : Fin n, I p l →
      readsAtMost C (n+n) (setList (edge p l)) k = true := by
  constructor
  · intro hc p l inc
    exact hc _ ((prime_iff_edge h _).mpr ⟨p,l,inc,rfl⟩)
  · intro hc S prime
    obtain ⟨p,l,inc,rfl⟩ := (prime_iff_edge h S).mp prime
    exact hc p l inc

theorem list_edge {n : ℕ} (p l : Fin n) :
    setList (edge p l) = [p.val,n + l.val] := by
  have sorted : ((List.finRange (n+n)).Pairwise (fun a b => a.val < b.val)) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem_finRange,Fin.val_cast] using hij
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · unfold setList
    exact List.pairwise_map.mpr (sorted.filter _)
  · simp
    omega
  · intro a
    unfold setList
    constructor
    · intro h
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      have hm : b ∈ edge p l := of_decide_eq_true (List.mem_filter.mp hb).2
      rcases Finset.mem_insert.mp hm with rfl | h
      · exact List.mem_cons_self
      · obtain rfl := Finset.mem_singleton.mp h
        exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact List.mem_map.mpr ⟨Fin.castAdd n p,
          List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ((left_mem p l p).mpr rfl)⟩,rfl⟩
      · exact List.mem_map.mpr ⟨Fin.natAdd n l,
          List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ((right_mem p l l).mpr rfl)⟩,rfl⟩

end IncidenceRead

/- James Adams. Keep just the nine count pairs in {0,1,2}² for a read-two
   test on two distinct inputs. -/
namespace IncidenceRead.PairTable

open PEqualNP.ReadK PEqualNP.CircuitLowerBounds

abbrev Vectors := List (List ℕ)
abbrev Cell := Fin 3 × Fin 3
abbrev Table := Cell → Bool

def vec (p : Cell) := [p.1.val, p.2.val]
def project (A : Vectors) : Table := fun p => decide (vec p ∈ A)
def blank : Table := fun _ => false
def join (a b : Table) : Table := fun p => a p || b p
def combine (a b : Table) : Table := fun p => decide (∃ u v : Cell,
  a u = true ∧ b v = true ∧ u.1.val + v.1.val = p.1.val ∧ u.2.val + v.2.val = p.2.val)

def Two (A : Vectors) : Prop := ∀ x ∈ A, ∃ i j : ℕ, x = [i,j]

private theorem mem_insert (x y : List ℕ) (A : Vectors) :
    x ∈ insertNew A y ↔ x ∈ A ∨ x = y := by
  unfold insertNew
  split_ifs with hy
  · constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hy
  · simp

private theorem mem_extend (x : List ℕ) (A B : Vectors) :
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons v vs ih => simp only [List.foldl_cons, ih, mem_insert, List.mem_cons]; tauto

private theorem mem_and (x : List ℕ) (A B : Vectors) :
    x ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd 2 u v = x := by
  simp [andStep, mem_extend]

theorem combine_exact (A B : Vectors) (ha : Two A) (hb : Two B) :
    project (andStep 2 A B) = combine (project A) (project B) := by
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [project,combine,decide_eq_true_eq,mem_and]
  constructor
  · rintro ⟨u,hu,v,hv,eq⟩
    obtain ⟨a,b,rfl⟩ := ha u hu
    obtain ⟨c,d,rfl⟩ := hb v hv
    simp [capAdd,vec] at eq
    obtain ⟨e₁,e₂⟩ := eq
    have h₁ := p.1.isLt
    have h₂ := p.2.isLt
    have ac : a+c = p.1.val := by omega
    have bd : b+d = p.2.val := by omega
    exact ⟨(⟨a,by omega⟩,⟨b,by omega⟩),(⟨c,by omega⟩,⟨d,by omega⟩),hu,hv,ac,bd⟩
  · rintro ⟨u,v,hu,hv,e₁,e₂⟩
    refine ⟨vec u,hu,vec v,hv,?_⟩
    simp [vec,capAdd,e₁,e₂]

theorem join_exact (A B : Vectors) :
    project (B.foldl insertNew A) = join (project A) (project B) := by
  funext p
  apply Bool.eq_iff_iff.mpr
  simp [project,join,mem_extend]

private theorem two_join {A B : Vectors} (ha : Two A) (hb : Two B) :
    Two (B.foldl insertNew A) := by
  intro x hx
  rcases (mem_extend x A B).mp hx with h | h
  · exact ha x h
  · exact hb x h

private theorem two_and {A B : Vectors} (ha : Two A) (hb : Two B) :
    Two (andStep 2 A B) := by
  intro x hx
  obtain ⟨u,hu,v,hv,rfl⟩ := (mem_and x A B).mp hx
  obtain ⟨a,b,rfl⟩ := ha u hu
  obtain ⟨c,d,rfl⟩ := hb v hv
  exact ⟨_,_,rfl⟩

private theorem project_nil : project [] = blank := by
  funext p
  simp [project,blank]

private theorem two_nil : Two [] := by simp [Two]

private theorem two_zero : Two [[0,0]] := by simp [Two]

private theorem projected_get (R : List Vectors) (i : ℕ) :
    (R.map project).getD i blank = project (R.getD i []) := by
  induction R generalizing i with
  | nil => simp [List.getD_eq_getElem?_getD,project_nil]
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem two_get (R : List Vectors) (h : ∀ A ∈ R, Two A) (i : ℕ) :
    Two (R.getD i []) := by
  induction R generalizing i with
  | nil => simpa [List.getD_eq_getElem?_getD] using two_nil
  | cons v vs ih =>
    cases i with
    | zero => exact h v (by simp)
    | succ i => exact ih (fun A ha => h A (by simp [ha])) i

private theorem or_fold (L : List Vectors) (A : Vectors) :
    (L.map project).foldl join (project A) =
    project (L.foldl (fun acc B => B.foldl insertNew acc) A) := by
  induction L generalizing A with
  | nil => rfl
  | cons B L ih =>
    simp only [List.map_cons,List.foldl_cons,← join_exact]
    exact ih _

private theorem two_or_fold (L : List Vectors) (h : ∀ B ∈ L, Two B) (A : Vectors) (ha : Two A) :
    Two (L.foldl (fun acc B => B.foldl insertNew acc) A) := by
  induction L generalizing A with
  | nil => exact ha
  | cons B L ih =>
    exact ih (fun z hz => h z (by simp [hz])) _ (two_join ha (h B (by simp)))

private theorem and_fold (L : List Vectors) (h : ∀ B ∈ L, Two B) (A : Vectors) (ha : Two A) :
    (L.map project).foldl combine (project A) = project (L.foldl (andStep 2) A) := by
  induction L generalizing A with
  | nil => rfl
  | cons B L ih =>
    have hb := h B (by simp)
    simp only [List.map_cons,List.foldl_cons,← combine_exact A B ha hb]
    exact ih (fun z hz => h z (by simp [hz])) _ (two_and ha hb)

private theorem two_and_fold (L : List Vectors) (h : ∀ B ∈ L, Two B) (A : Vectors) (ha : Two A) :
    Two (L.foldl (andStep 2) A) := by
  induction L generalizing A with
  | nil => exact ha
  | cons B L ih =>
    exact ih (fun z hz => h z (by simp [hz])) _ (two_and ha (h B (by simp)))

private def referenceGate (R : List Vectors) (g : Gate) : Vectors :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | .or => ins.foldl (fun acc B => B.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [[0,0]]
  | _ => []

def tableGate (R : List Table) (g : Gate) : Table :=
  let ins := g.inputs.map fun i => R.getD i blank
  match g.op with
  | .or => ins.foldl join blank
  | .and => ins.foldl combine (project [[0,0]])
  | _ => blank

private theorem gate_ok (R : List Vectors) (h : ∀ A ∈ R, Two A) (g : Gate) :
    tableGate (R.map project) g = project (referenceGate R g) ∧ Two (referenceGate R g) := by
  let ins := g.inputs.map (fun i => R.getD i [])
  have hits : ∀ B ∈ ins, Two B := by
    intro B hb
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact two_get R h i
  have inputs : (g.inputs.map fun i => (R.map project).getD i blank) = ins.map project := by
    unfold ins
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact projected_get R i
  unfold tableGate referenceGate
  simp only [inputs]
  change (match g.op with
    | .or => (ins.map project).foldl join blank
    | .and => (ins.map project).foldl combine (project [[0,0]])
    | _ => blank) = project (match g.op with
    | .or => ins.foldl (fun acc B => B.foldl insertNew acc) []
    | .and => ins.foldl (andStep 2) [[0,0]]
    | _ => []) ∧ _
  cases e : g.op with
  | or => exact ⟨project_nil ▸ or_fold ins [], two_or_fold ins hits [] two_nil⟩
  | and => exact ⟨and_fold ins hits _ two_zero, two_and_fold ins hits _ two_zero⟩
  | _ => exact ⟨project_nil.symm,two_nil⟩

private theorem gates_ok (G : List Gate) (R : List Vectors) (h : ∀ A ∈ R, Two A) :
    G.foldl (fun W g => W ++ [tableGate W g]) (R.map project) =
    (G.foldl (fun W g => W ++ [referenceGate W g]) R).map project := by
  induction G generalizing R with
  | nil => rfl
  | cons g G ih =>
    have step := gate_ok R h g
    simp only [List.foldl_cons,step.1]
    rw [show R.map project ++ [project (referenceGate R g)] =
      (R ++ [referenceGate R g]).map project by simp]
    apply ih
    intro A ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h A ha
    · have e : A = referenceGate R g := by simpa using ha
      exact e ▸ step.2

def tables (C : Circuit) (n u v : ℕ) : List Table :=
  C.gates.foldl (fun W g => W ++ [tableGate W g])
    (((List.range n).map (leafVectors [u,v] 2)).map project)

theorem tables_exact (C : Circuit) (n u v : ℕ) :
    tables C n u v = (readVectors C n [u,v] 2).map project := by
  apply gates_ok
  intro A ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  unfold leafVectors
  split
  · simp [Two]
  · exact two_nil

private theorem all_two (G : List Gate) (R : List Vectors) (h : ∀ A ∈ R, Two A) :
    ∀ A ∈ G.foldl (fun W g => W ++ [referenceGate W g]) R, Two A := by
  induction G generalizing R with
  | nil => exact h
  | cons g G ih =>
    apply ih
    intro A ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h A ha
    · have e : A = referenceGate R g := by simpa using ha
      exact e ▸ (gate_ok R h g).2

private theorem vectors_two (C : Circuit) (n u v : ℕ) :
    ∀ A ∈ readVectors C n [u,v] 2, Two A := by
  apply all_two
  intro A ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  unfold leafVectors
  split
  · simp [Two]
  · exact two_nil

def accepts (C : Circuit) (n u v : ℕ) : Bool :=
  decide (∃ p : Cell, (tables C n u v).getD C.output blank p = true)

theorem accepts_exact (C : Circuit) (n u v : ℕ) :
    accepts C n u v = readsAtMost C n [u,v] 2 := by
  apply Bool.eq_iff_iff.mpr
  unfold accepts readsAtMost
  rw [tables_exact,projected_get]
  simp only [project,decide_eq_true_eq,List.any_eq_true,List.all_eq_true]
  let R := readVectors C n [u,v] 2
  have well := two_get R (vectors_two C n u v) C.output
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨vec p,hp,?_⟩
    simp [vec]
    omega
  · rintro ⟨w,hw,hb⟩
    obtain ⟨a,b,rfl⟩ := well w hw
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    exact ⟨(⟨a,by omega⟩,⟨b,by omega⟩),hw⟩

end IncidenceRead.PairTable

namespace IncidenceRead

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

/-- For a circuit already known to compute the incidence function, only its
    actual incidence edges require read tests. Each gate uses a nine-cell table. -/
theorem read_two_iff_pair_tables {n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {C : Circuit} (h : Computes I C) :
    IsReadK (n+n) C 2 ↔ ∀ p l : Fin n, I p l →
      PairTable.accepts C (n+n) p.val (n + l.val) = true := by
  simpa only [list_edge,PairTable.accepts_exact] using read_iff_edges h 2

end IncidenceRead
#print axioms IncidenceRead.read_two_iff_pair_tables
