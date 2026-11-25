import DivCount
import Column
import SourceCoverage

/-! Convert a live trace with one-use occurrences into the K4 finite catalog.
The graph disjointness argument uses the occurrence lemmas from harshb16's
L-meta-9672 (PR 16368). All rule arithmetic uses the official CP representation. -/

namespace K4TraceTree
open K4Column
open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path

/-- In a trace using each non-root occurrence once, the subgraphs feeding the
two inputs of an addition have no common occurrence, even for repeated premises. -/
theorem forkDisjoint {incoming : ℕ → List ℕ} {live : Finset ℕ} {root node a b t : ℕ}
    (subset : live ⊆ Finset.range (root+1))
    (order : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (once : ∀ i ∈ live, i ≠ root → uses incoming live i = 1)
    (ht : t ∈ live) (hn : node ∈ live) (ins : incoming node = [a,b])
    (ha : Reach incoming live t a) (hb : Reach incoming live t b) : False := by
  have ma : a ∈ incoming node := by simp [ins]
  have mb : b ∈ incoming node := by simp [ins]
  have htn : Reach incoming live t node := .tail ha ⟨hn,ma⟩
  have lt : t < node := lt_of_le_of_lt (reach_le order ha) (order node hn a ma)
  obtain ⟨u, _, only, agree⟩ := affected_unique_input subset order
    (fun i hi => once i (reach_mem_live ht hi)) htn (by omega)
  have eqa := agree a ma ha
  have eqb := agree b mb hb
  subst a
  subst b
  simp [ins] at only

/-- All set bits of the support come from the unique source of their edge. -/
def Supported (incoming : ℕ → List ℕ) (live : Finset ℕ) (source : Fin 6 → ℕ)
    (node mask : ℕ) : Prop :=
  ∀ bit, mask.testBit bit = true → ∃ k : Fin 6, k.val = bit ∧ Reach incoming live (source k) node

private theorem edgeMask : ∀ k : Fin 6, (edge k).1 = 2^k.val := by decide +kernel

private theorem liftSupport {ins : ℕ → List ℕ} {live : Finset ℕ} {source : Fin 6 → ℕ}
    {a i mask} (hi : i ∈ live) (mem : a ∈ ins i) (h : Supported ins live source a mask) :
    Supported ins live source i mask := by
  intro bit hb
  obtain ⟨k, hk, reach⟩ := h bit hb
  exact ⟨k, hk, .tail reach ⟨hi,mem⟩⟩

theorem structural {ins : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    {line : ℕ → Line} {source : Fin 6 → ℕ}
    (subset : live ⊆ Finset.range (root+1))
    (closed : ∀ i ∈ live, ∀ a ∈ ins i, a ∈ live)
    (order : ∀ i ∈ live, ∀ j ∈ ins i, j < i)
    (once : ∀ i ∈ live, i ≠ root → uses ins live i = 1)
    (present : ∀ k, source k ∈ live)
    (rules : ∀ i ∈ live,
      (∃ k, source k = i ∧ line i = (edge k).2) ∨
      (∃ a b, ins i = [a,b] ∧ line i = add (line a) (line b)) ∨
      (∃ a d, ins i = [a] ∧ 0 < d ∧ divisible (line a) d ∧ line i = divide (line a) d)) :
    ∀ i ∈ live, ∃ m, ReadOnce (m,line i) ∧ Supported ins live source i m := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    rcases rules i hi with ⟨k, rfl, hk⟩ | ⟨a,b,hin,heq⟩ | ⟨a,d,hin,hd,hdiv,heq⟩
    · refine ⟨(edge k).1, hk ▸ ReadOnce.leaf k, ?_⟩
      intro bit hb
      rw [edgeMask, Nat.testBit_two_pow] at hb
      exact ⟨k, of_decide_eq_true hb, .refl⟩
    · have ha : a ∈ ins i := by simp [hin]
      have hb : b ∈ ins i := by simp [hin]
      obtain ⟨m, hm, sm⟩ := ih a (order i hi a ha) (closed i hi a ha)
      obtain ⟨n, hn, sn⟩ := ih b (order i hi b hb) (closed i hi b hb)
      have disjoint : m &&& n = 0 := by
        apply Nat.eq_of_testBit_eq
        intro bit
        rw [Nat.testBit_and, Nat.zero_testBit]
        by_cases hm' : m.testBit bit = true
        · by_cases hn' : n.testBit bit = true
          · obtain ⟨k,hk,ra⟩ := sm bit hm'
            obtain ⟨l,hl,rb⟩ := sn bit hn'
            have eq : k = l := Fin.ext (hk.trans hl.symm)
            subst l
            exact False.elim (forkDisjoint subset order once (present k) hi hin ra rb)
          · simp [hn']
        · simp [hm']
      refine ⟨m ||| n, heq ▸ ReadOnce.join hm hn disjoint, ?_⟩
      intro bit hbit
      rw [Nat.testBit_or, Bool.or_eq_true] at hbit
      exact hbit.elim (liftSupport hi ha sm bit) (liftSupport hi hb sn bit)
    · have ha : a ∈ ins i := by simp [hin]
      obtain ⟨m, hm, sm⟩ := ih a (order i hi a ha) (closed i hi a ha)
      exact ⟨m, heq ▸ ReadOnce.cut d hm hd hdiv, liftSupport hi ha sm⟩


open PEqualNP.Search CliqueEdges
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch (Rule parents legalRule)
open CPTargetTrace (ruleKind)

/-- Interpret a positive upper-bound tuple as an official signed CP inequality. -/
def signed (x : Line) : L :=
  (fun v => -((![x.a,x.b,x.c,x.d] v : ℕ) : ℤ), -(x.rhs : ℤ))

def decode (e : L) : Line :=
  ⟨(-e.1 0).toNat, (-e.1 1).toNat, (-e.1 2).toNat, (-e.1 3).toNat, (-e.2).toNat⟩

theorem decodeSigned (x : Line) : decode (signed x) = x := by
  cases x
  simp [decode, signed]

theorem signedEdge (k : Fin 6) : clauseCP (pairClause k) = signed (edge k).2 := by
  apply Prod.ext
  · funext v
    exact (by decide +kernel : ∀ k : Fin 6, ∀ v : Fin 4,
      (clauseCP (pairClause k)).1 v = (signed (edge k).2).1 v) k v
  · exact (by decide +kernel : ∀ k : Fin 6, (clauseCP (pairClause k)).2 = (signed (edge k).2).2) k

private theorem signedAdd (x y : Line) :
    ((signed x).1 + (signed y).1, (signed x).2 + (signed y).2) = signed (add x y) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [signed, add, add_comm]
  · simp [signed, add, add_comm]

private theorem signedCut (x : Line) (d : ℕ)
    (dvd : ∀ i, (d : ℤ) ∣ (signed x).1 i) :
    divisible x d ∧
    ((fun v => (signed x).1 v / (d : ℤ)), -((-(signed x).2)/(d : ℤ))) = signed (divide x d) := by
  have facts : ∀ i : Fin 4, d ∣ ![x.a,x.b,x.c,x.d] i := by
    intro i
    exact Int.natCast_dvd_natCast.mp (Int.dvd_neg.mp (dvd i))
  refine ⟨⟨facts 0, facts 1, facts 2, facts 3⟩, Prod.ext ?_ ?_⟩
  · funext i
    have h := Int.neg_ediv_of_dvd (Int.natCast_dvd_natCast.mpr (facts i))
    fin_cases i <;> simpa [signed, divide] using h
  · simp [signed,divide]

/-- Official signed rule trace, normalized to the three admissible rule cases
under the leaf bijection and zero-multiplication conclusions. -/
theorem ofOfficial {rule : ℕ → Rule Var} {read : ℕ → L} {live : Finset ℕ} {root : ℕ}
    {source : Fin 6 → ℕ}
    (subset : live ⊆ Finset.range (root+1))
    (closed : ∀ i ∈ live, ∀ a ∈ parents (rule i), a ∈ live)
    (order : ∀ i ∈ live, ∀ j ∈ parents (rule i), j < i)
    (once : ∀ i ∈ live, i ≠ root → uses (fun j => parents (rule j)) live i = 1)
    (present : ∀ k, source k ∈ live)
    (sources : ∀ i ∈ live, ruleKind (rule i) = .source →
      ∃ k, source k = i ∧ read i = clauseCP (pairClause k))
    (noMul : ∀ i ∈ live, ruleKind (rule i) ≠ .multiplication)
    (legal : ∀ i ∈ live, legalRule edges i read (read i) (rule i)) :
    ∀ i ∈ live, ∃ m, ReadOnce (m,decode (read i)) := by
  have steps : ∀ i ∈ live,
      (∃ k, source k = i ∧ read i = signed (edge k).2) ∨
      (∃ a b, parents (rule i) = [a,b] ∧ read i = ((read a).1+(read b).1,(read a).2+(read b).2)) ∨
      (∃ (a d : ℕ), parents (rule i) = [a] ∧ 0 < d ∧ (∀ v, (d:ℤ) ∣ (read a).1 v) ∧
        read i = (fun v => (read a).1 v / (d:ℤ), -((-(read a).2)/(d:ℤ)))) := by
    intro i hi
    have le := legal i hi
    rcases hr : rule i with ax | (⟨a,b⟩ | (⟨a,k⟩ | ⟨a,d⟩))
    · obtain ⟨k,hk,he⟩ := sources i hi (by simp [hr,ruleKind])
      exact .inl ⟨k,hk,he.trans (signedEdge k)⟩
    · rw [hr] at le
      exact .inr (.inl ⟨a,b,by simp [parents],le.2.2⟩)
    · exact False.elim (noMul i hi (by simp [hr,ruleKind]))
    · rw [hr] at le
      exact .inr (.inr ⟨a,d,by simp [parents],le.2⟩)
  have actual : ∀ i ∈ live, read i = signed (decode (read i)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      suffices h : ∃ l, read i = signed l by
        obtain ⟨l,hl⟩ := h
        rw [hl, decodeSigned]
      rcases steps i hi with ⟨k,_,he⟩ | ⟨a,b,hin,he⟩ | ⟨a,d,hin,_,hdv,he⟩
      · exact ⟨_,he⟩
      · have ha : a ∈ parents (rule i) := by simp [hin]
        have hb : b ∈ parents (rule i) := by simp [hin]
        rw [ih a (order i hi a ha) (closed i hi a ha), ih b (order i hi b hb) (closed i hi b hb)] at he
        exact ⟨_,he.trans (signedAdd _ _)⟩
      · have ha : a ∈ parents (rule i) := by simp [hin]
        have eq := ih a (order i hi a ha) (closed i hi a ha)
        rw [eq] at hdv he
        exact ⟨_,he.trans (signedCut _ _ hdv).2⟩
  have laws : ∀ i ∈ live,
      (∃ k, source k = i ∧ decode (read i) = (edge k).2) ∨
      (∃ a b, parents (rule i) = [a,b] ∧ decode (read i) = add (decode (read a)) (decode (read b))) ∨
      (∃ (a d : ℕ), parents (rule i) = [a] ∧ 0 < d ∧ divisible (decode (read a)) d ∧
        decode (read i) = divide (decode (read a)) d) := by
    intro i hi
    rcases steps i hi with ⟨k,hk,he⟩ | ⟨a,b,hin,he⟩ | ⟨a,d,hin,hd,hdv,he⟩
    · exact .inl ⟨k,hk, by rw [he,decodeSigned]⟩
    · rw [actual a (closed i hi a (by simp [hin])), actual b (closed i hi b (by simp [hin]))] at he
      exact .inr (.inl ⟨a,b,hin, by rw [he,signedAdd,decodeSigned]⟩)
    · have eq := actual a (closed i hi a (by simp [hin]))
      rw [eq] at hdv he
      obtain ⟨dv,f⟩ := signedCut _ _ hdv
      exact .inr (.inr ⟨a,d,hin,hd,dv,by rw [he,f,decodeSigned]⟩)
  intro i hi
  obtain ⟨m, hm, _⟩ := structural subset closed order once present laws i hi
  exact ⟨m,hm⟩

open CPTargetTrace (countKind capacityBudget)

theorem budgetContradiction {rule : ℕ → Rule Var} {read : ℕ → L} {live : Finset ℕ} {root : ℕ}
    (member : root ∈ live) (target : read root = cap) (subset : live ⊆ Finset.range (root+1))
    (small : live.card ≤ 13)
    (legal : ∀ i ∈ live, legalRule edges i read (read i) (rule i))
    (closed : PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch.closedUnder (fun i => parents (rule i)) live)
    (order : ∀ i j, j ∈ parents (rule i) → j < i)
    (used : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (coverage : ∀ k : Fin 6, ∃ i ∈ live, ruleKind (rule i) = .source ∧ read i = clauseCP (pairClause k)) :
    False := by
  classical
  choose source present kind labels using coverage
  let leaves := live.filter (fun i => ruleKind (rule i) = .source)
  have inj : Function.Injective source := by
    intro k l e
    exact sixDistinct ((labels k).symm.trans ((congrArg read e).trans (labels l)))
  have inc : Finset.univ.image source ⊆ leaves := by
    intro x h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨present k, kind k⟩
  have six : (Finset.univ.image source).card = 6 := by
    rw [Finset.card_image_of_injective _ inj]
    decide
  have lows : 6 ≤ countKind live rule .source := six ▸ Finset.card_le_card inc
  have cuts := CliqueDivisions.atLeastTwo member target legal closed
  obtain ⟨_, count, _, _, noMul, once⟩ :=
    capacityBudget member subset closed order used small lows cuts
  have exhaust : Finset.univ.image source = leaves :=
    Finset.eq_of_subset_of_card_le inc (by change countKind live rule .source ≤ _; omega)
  have classes (i : ℕ) (hi : i ∈ live) (h : ruleKind (rule i) = .source) :
      ∃ k, source k = i ∧ read i = clauseCP (pairClause k) := by
    have mem : i ∈ leaves := Finset.mem_filter.mpr ⟨hi,h⟩
    rw [← exhaust] at mem
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp mem
    exact ⟨k,rfl,labels k⟩
  have noMult (i) (hi : i ∈ live) (h : ruleKind (rule i) = .multiplication) : False := by
    have he : (live.filter fun n => ruleKind (rule n) = .multiplication) = ∅ :=
      Finset.card_eq_zero.mp noMul
    have mem : i ∈ live.filter (fun n => ruleKind (rule n) = .multiplication) :=
      Finset.mem_filter.mpr ⟨hi,h⟩
    rw [he] at mem
    exact Finset.notMem_empty _ mem
  obtain ⟨s, tree⟩ := ofOfficial subset closed (fun i _ => order i) once present
    classes noMult legal root member
  rw [target] at tree
  exact noReadOnceCapacity s tree

/-- Every official cutting-planes derivation of K4 clique capacity from its six pair
clauses takes at least fourteen lines, including its source and Boolean axioms. -/
theorem capacityFourteen {π : List L} (h : IsCPDerivation edges π) (hc : cap ∈ π) :
    14 ≤ π.length := by
  by_contra! short
  obtain ⟨root, rule, live, _, target, member, subset, size, legal, closed, order, used⟩ :=
    CPTargetTrace.forLine h hc
  exact budgetContradiction member target subset (by omega) legal closed order used
    (CliqueSources.coverage member target legal closed)

end K4TraceTree

#print axioms K4TraceTree.capacityFourteen
