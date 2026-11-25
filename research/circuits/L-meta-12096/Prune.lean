import SignedFrontier

namespace Row12096Prune
open Row12096Signed

private theorem singles_preserve {P : W → Prop} {ws : List W}
    (h : ∀ w ∈ ws, P w) {q : W × List W} (hq : q ∈ singles ws) :
    P q.1 ∧ ∀ w ∈ q.2, P w := by
  induction ws generalizing q with
  | nil => simp [singles] at hq
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr : ∀ w ∈ rest, P w := fun w hw => h w (List.mem_cons_of_mem _ hw)
    rcases List.mem_cons.mp hq with rfl | hm
    · exact ⟨ha, hr⟩
    · obtain ⟨⟨b, t⟩, hb, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hp, ht⟩ := ih hr hb
      exact ⟨hp, fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ ha) (ht w)⟩

private theorem pairs_preserve {P : W → Prop} {ws : List W}
    (h : ∀ w ∈ ws, P w) {q : W × W × List W} (hq : q ∈ pairs ws) :
    P q.1 ∧ P q.2.1 ∧ ∀ w ∈ q.2.2, P w := by
  induction ws generalizing q with
  | nil => simp [pairs] at hq
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr : ∀ w ∈ rest, P w := fun w hw => h w (List.mem_cons_of_mem _ hw)
    rcases List.mem_append.mp hq with hm | hm
    · obtain ⟨⟨b,t⟩, hb,rfl⟩ := List.mem_map.mp hm
      exact ⟨ha, singles_preserve hr hb⟩
    · obtain ⟨⟨b,c,t⟩, hb,rfl⟩ := List.mem_map.mp hm
      obtain ⟨hp, hp', ht⟩ := ih hr hb
      exact ⟨hp, hp', fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ ha) (ht w)⟩

/-- Every search continuation preserves a predicate shared by all current
wires and closed under each of the four signed binary operations. -/
theorem optimized_false_of_closed {P : W → Prop}
    (closed : ∀ a b, P a → P b → ∀ z ∈ ops a b, P z)
    (ng : ¬P goal) (nn : ¬P (~~~goal)) (k extra : ℕ) (ws : List W)
    (hw : ∀ w ∈ ws, P w) : optimized k extra ws = false := by
  have ht : ws ≠ [goal] := fun h => ng (hw goal (by simp [h]))
  have hn : ws ≠ [~~~goal] := fun h => nn (hw _ (by simp [h]))
  induction k generalizing extra ws with
  | zero => simp [optimized, ht, hn]
  | succ k ih =>
    simp only [optimized, Bool.or_eq_false_iff]
    refine ⟨⟨by simpa using ht, by simpa using hn⟩, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨⟨a,b,r⟩,hpair,hdisp⟩ := List.any_eq_true.mp hit
    obtain ⟨ha,hb,hr⟩ := pairs_preserve hw hpair
    obtain ⟨z,hz,hh⟩ := List.any_eq_true.mp hdisp
    have hp := closed a b ha hb z hz
    have invoke (e : ℕ) (xs : List W) (hx : ∀ w ∈ xs, P w) :
        optimized k e xs = false :=
      ih e xs hx (fun eq => ng (hx _ (by simp [eq]))) (fun eq => nn (hx _ (by simp [eq])))
    have add {x : W} {l : List W} (hx : P x) (hl : ∀ w ∈ l, P w) :
        ∀ w ∈ x :: l, P w := by
      intro w hw'
      exact (List.mem_cons.mp hw').elim (fun eq => eq ▸ hx) (hl w)
    have h0 := invoke extra _ (add hp hr)
    have h1 := invoke (extra-1) _ (add hp (add ha hr))
    have h2 := invoke (extra-1) _ (add hp (add hb hr))
    have h3 := invoke (extra-2) _ (add hp (add ha (add hb hr)))
    simp [h0,h1,h2,h3] at hh

/-- Positions can be any two of the 256 encoded bits; they need not be a
paired positive/negative comparison in cuts. -/
theorem optimized_false_of_collision (i j : Fin 256)
    (hgoal : goal.getLsbD i.val ≠ goal.getLsbD j.val)
    (k extra : ℕ) (ws : List W)
    (hit : ∀ w ∈ ws, w.getLsbD i.val = w.getLsbD j.val) :
    optimized k extra ws = false := by
  apply optimized_false_of_closed (P := fun w => w.getLsbD i.val = w.getLsbD j.val) _ hgoal _ k extra ws hit
  · intro a b ha hb z hz
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        i.isLt, j.isLt, decide_true, Bool.true_and, ha, hb]
  · simpa [BitVec.getLsbD_not, i.isLt, j.isLt] using hgoal

abbrev Comparison := Fin 256 × Fin 256

/-- A supplied comparison certifies failure when it has opposite output
labels and every currently available wire takes the same value on its two
positions. A single successful comparison suffices. -/
def collides (checks : List Comparison) (ws : List W) : Bool :=
  checks.any fun (i, j) =>
    goal.getLsbD i.val != goal.getLsbD j.val &&
    ws.all (fun w => w.getLsbD i.val == w.getLsbD j.val)

theorem collides_sound (checks : List Comparison) (ws : List W)
    (h : collides checks ws = true) (k extra : ℕ) : optimized k extra ws = false := by
  obtain ⟨⟨i,j⟩, _, hit⟩ := List.any_eq_true.mp h
  obtain ⟨labels, eqs⟩ := Bool.and_eq_true_iff.mp hit
  apply optimized_false_of_collision i j (by simpa using labels) k extra ws
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp eqs w hw)

/-- All opposite row labels, using one encoded position per six-input row. -/
def allOpposite : List Comparison :=
  let rows := List.ofFn rowPosition
  (rows.filter (fun i => goal.getLsbD i.val)).flatMap fun i =>
    (rows.filter (fun j => !goal.getLsbD j.val)).map fun j => (i,j)

/-- The frontier only needs to contain children which pass all additional
prunes. A prune may use the slack and the state; soundness is required only
at the child depth being proved. -/
theorem rejectPrunedLayer {k : ℕ} {s : State} {states : List State}
    (dead : ℕ → List W → Bool)
    (sound : ∀ e ws, dead e ws = true → optimized k e ws = false)
    (covered : nextLayer (fun e ws => !dead e ws && outsideList states e ws) s.1 s.2 = false)
    (sub : ∀ p ∈ states, optimized k p.1 p.2 = false) : optimized (k+1) s.1 s.2 = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  change nextLayer (optimized k) s.1 s.2 = true at hit
  apply Bool.noConfusion (covered.symm.trans (layer_increases ?_ hit))
  intro e ws h
  have hd : dead e ws = false := Bool.eq_false_iff.mpr fun t =>
    Bool.noConfusion ((sound e ws t).symm.trans h)
  have hm : (e,ws) ∉ states := fun p => Bool.noConfusion ((sub (e,ws) p).symm.trans h)
  simp [hd, outsideList, hm]

end Row12096Prune
#print axioms Row12096Prune.collides_sound
#print axioms Row12096Prune.rejectPrunedLayer
#print axioms Row12096Prune.optimized_false_of_collision
