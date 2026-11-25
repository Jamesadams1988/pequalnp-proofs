import CleanCover
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L204

namespace ForestIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem different_sides {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have q := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at q
  have := p.isLt
  omega

/-- The undirected graph obtained from the two labelled sides of an incidence relation. -/
def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
    (v = Fin.castAdd N p ∧ u = Fin.natAdd N l))
  symm := ⟨by rintro u v ⟨p,l,h,d⟩; exact ⟨p,l,h,d.symm⟩⟩
  loopless := ⟨by rintro u ⟨p,l,_,⟨a,b⟩|⟨a,b⟩⟩ <;> exact different_sides p l (a.symm.trans b)⟩

def incidence {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N+N) → Bool) : Prop :=
  ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true

def liveEdge {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true

theorem edge_iff {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N+N) → Bool) :
    liveEdge (graph I) x ↔ incidence I x := by
  constructor
  · rintro ⟨u,v,⟨p,l,h,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩,hu,hv⟩
    · exact ⟨p,l,h,hu,hv⟩
    · exact ⟨p,l,h,hv,hu⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨_,_,⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩

private theorem no_singleton {N : ℕ} (I : Fin N → Fin N → Prop) (v : Fin (N+N)) :
    ¬incidence I (fun k => decide (k = v)) := by
  rintro ⟨p,l,_,hp,hl⟩
  simp only [decide_eq_true_eq] at hp hl
  exact different_sides p l (hp.trans hl.symm)

/-- The two AND conditions and the cost guarantee in the original desk statement. -/
def Normal {N : ℕ} (I : Fin N → Fin N → Prop) (C D : Circuit) : Prop :=
  Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
  (∀ z, circuitFun (N+N) D z = true ↔ incidence I z) ∧
  (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ z : Fin (N+N) → Bool,
    (D.wires (List.ofFn z)).getD (N+N+j) false = true →
    (D.wires (List.ofFn (fun k => decide (k.val < N) && z k))).getD (N+N+j) false = true ∨
    (D.wires (List.ofFn (fun k => decide (N ≤ k.val) && z k))).getD (N+N+j) false = true ∨ incidence I z) ∧
  (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
    (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
    ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.natAdd N l)))).getD (N+N+j) false = false)

def Productive {n : ℕ} (G : SimpleGraph (Fin n)) (D : Circuit) : Prop :=
  ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
    (D.wires (List.ofFn x)).getD (n+j) false = true → liveEdge G x

/-- The interface of the constructive star-cover theorem. -/
def CoverUpper : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)), (∃ i j, G.Adj i j) → (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      (∀ x : Fin n → Bool, circuitFun n D x = true ↔ liveEdge G x) ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card ∧ Productive G D

private theorem coverConstruction : CoverUpper := by
  intro n G dec T edge cover
  obtain ⟨D,hm,hback,heval,hsize,hprod⟩ := CleanCover.edge_upper_clean n G T edge cover
  refine ⟨D,hm,hback,?_,hsize,hprod⟩
  intro x
  rw [heval]
  simp [liveEdge]

private theorem empty_case {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (h : ¬∃ i j, (graph I).Adj i j) : ∃ D, Normal I C D := by
  let D : Circuit := ⟨[],N+N⟩
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · simp [D,Monotone2]
  · simp [D,ReadsBack]
  · simp [D,Circuit.size]
  · intro z
    have hn : ¬incidence I z := fun he => by
      obtain ⟨i,j,a,_,_⟩ := (edge_iff I z).mpr he
      exact h ⟨i,j,a⟩
    simp [D,circuitFun,Circuit.eval,Circuit.wires,hn]
  · simp [D]
  · simp [D]

private theorem productive_normal {N : ℕ} {I : Fin N → Fin N → Prop} {C D : Circuit}
    (mono : Monotone2 D) (back : ReadsBack (N+N) D) (sz : D.size ≤ C.size)
    (eval : ∀ z, circuitFun (N+N) D z = true ↔ liveEdge (graph I) z)
    (prod : Productive (graph I) D) : Normal I C D := by
  refine ⟨mono,back,sz,fun z => (eval z).trans (edge_iff I z),?_,?_⟩
  · intro j hj ha z live
    exact Or.inr (Or.inr ((edge_iff I z).mp (prod j hj ha z live)))
  · intro j hj ha
    have h : ∀ v : Fin (N+N), (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k=v)))).getD (N+N+j) false = false := by
      intro v
      apply Bool.eq_false_iff.mpr
      intro live
      exact no_singleton I v ((edge_iff I _).mp (prod j hj ha _ live))
    exact ⟨fun p => h _,fun l => h _⟩

private theorem circuit_has_size {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin (N+N) → Bool, circuitFun (N+N) C x = true ↔ incidence I x)
    [DecidableRel (graph I).Adj] : HasCircuitSize (N+N) (fun x : Fin (N+N) → Bool => decide (∃ i j, (graph I).Adj i j ∧ x i = true ∧ x j = true)) C.size := by
  refine ⟨C,?_,le_rfl,?_⟩
  · intro g hg
    obtain ⟨hop,hl⟩ := mono g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
    exact hop.imp_right Or.inl
  · intro x
    apply Bool.eq_iff_iff.mpr
    exact (correct x).trans ((edge_iff I x).symm.trans (by simp [liveEdge]))

private theorem assemble (upper : CoverUpper) {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (lower : ∀ (T : Finset (Fin (N+N))), (∃ i j, (graph I).Adj i j) →
      (∀ U : Finset (Fin (N+N)), (∀ i j, (graph I).Adj i j → i ∈ U ∨ j ∈ U) → T.card ≤ U.card) →
      (graph I).edgeSet.ncard + T.card ≤ C.size + 1) : ∃ D, Normal I C D := by
  classical
  by_cases edge : ∃ i j, (graph I).Adj i j
  · let G := graph I
    let isCover (T : Finset (Fin (N+N))) := ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T
    have exists_cover : ∃ k : ℕ, ∃ T : Finset (Fin (N+N)), isCover T ∧ T.card = k := by
      exact ⟨_,Finset.univ,fun i _ _ => Or.inl (Finset.mem_univ i),rfl⟩
    obtain ⟨T,cover,card⟩ := Nat.find_spec exists_cover
    have minimal : ∀ U : Finset (Fin (N+N)), isCover U → T.card ≤ U.card := by
      intro U hu
      rw [card]
      exact Nat.find_min' exists_cover ⟨U,hu,rfl⟩
    have lb := lower T edge minimal
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at lb
    obtain ⟨D,dm,db,de,ds,dp⟩ := upper (N+N) G T edge cover
    change D.size + 1 ≤ (graph I).edgeFinset.card + T.card at ds
    exact ⟨D,productive_normal dm db (by omega) de dp⟩
  · exact empty_case I C edge

theorem forest_normalization {N : ℕ} (I : Fin N → Fin N → Prop)
    (C : Circuit) (forest : (graph I).IsAcyclic) (mono : Monotone2 C)
    (correct : ∀ x : Fin (N+N) → Bool, circuitFun (N+N) C x = true ↔ incidence I x) :
    ∃ D, Normal I C D := by
  classical
  apply assemble coverConstruction I C
  intro T edge minimal
  have lb := L104 (N+N) T.card C.size (graph I) forest edge minimal (circuit_has_size I C mono correct)
  simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using lb

/-- The long-thread family permits cycles of length at least seven and well-separated branch vertices. -/
theorem long_thread_normalization {N : ℕ} (I : Fin N → Fin N → Prop)
    (C : Circuit) (cycles : ∀ (v : Fin (N+N)) (w : (graph I).Walk v v), w.IsCycle → 7 ≤ w.length)
    (separation : ∀ (u v : Fin (N+N)), u ≠ v → 3 ≤ ((graph I).neighborSet u).ncard →
      3 ≤ ((graph I).neighborSet v).ncard → ∀ w : (graph I).Walk u v, 7 ≤ w.length)
    (mono : Monotone2 C)
    (correct : ∀ x : Fin (N+N) → Bool, circuitFun (N+N) C x = true ↔ incidence I x) :
    ∃ D, Normal I C D := by
  classical
  apply assemble coverConstruction I C
  intro T edge minimal
  let G := graph I
  have hc := circuit_has_size I C mono correct
  have heq : (fun x : Fin (N+N) → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin (N+N))), x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) =
      (fun x : Fin (N+N) → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x; simp
  have lb := L204 (N+N) T.card C.size G ∅ cycles separation (by simp) (Or.inr edge) minimal (heq.symm ▸ hc)
  simpa using lb

end ForestIncidence
