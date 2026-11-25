import SignedFrontier

/-! When there is no spare gate for reusing an operand, a subadditive
weight on signals bounds the weight of every possible output. The four-row
application detects a polarity conflict in one essential live wire. -/
namespace Row12096Polarity
open Row12096Signed

def total (weight : W → ℕ) (ws : List W) : ℕ := (ws.map weight).sum

private theorem splitOne (w : W → ℕ) (xs : List W) (p : W × List W)
    (h : p ∈ singles xs) : total w xs = w p.1 + total w p.2 := by
  induction xs generalizing p with
  | nil => simp [singles] at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [total]
    · obtain ⟨⟨b,rest⟩, hb, rfl⟩ := List.mem_map.mp h
      have hh := ih _ hb
      simp [total] at hh ⊢
      omega

private theorem splitTwo (w : W → ℕ) (xs : List W) (p : W × W × List W)
    (h : p ∈ pairs xs) : total w xs = w p.1 + w p.2.1 + total w p.2.2 := by
  induction xs generalizing p with
  | nil => simp [pairs] at h
  | cons a xs ih =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨⟨b,rest⟩, hb, rfl⟩ := List.mem_map.mp h
      have hh := splitOne w xs (b,rest) hb
      simp [total] at hh ⊢
      omega
    · obtain ⟨⟨b,c,rest⟩, hb, rfl⟩ := List.mem_map.mp h
      have hh := ih _ hb
      simp [total] at hh ⊢
      omega

/-- A zero-slack binary step consumes both operands permanently. It can
never increase total weight if each allowed operation is subadditive. -/
theorem zeroSlackLower (weight : W → ℕ)
    (subadd : ∀ a b, ∀ z ∈ ops a b, weight z ≤ weight a + weight b)
    (k : ℕ) (ws : List W)
    (pos : total weight ws < weight goal)
    (neg : total weight ws < weight (~~~goal)) : optimized k 0 ws = false := by
  induction k generalizing ws with
  | zero =>
    have hp : ws ≠ [goal] := by intro h; simp [h,total] at pos
    have hn : ws ≠ [~~~goal] := by intro h; simp [h,total] at neg
    simp [optimized,hp,hn]
  | succ k ih =>
    have hp : ws ≠ [goal] := by intro h; simp [h,total] at pos
    have hn : ws ≠ [~~~goal] := by intro h; simp [h,total] at neg
    simp only [optimized, Bool.or_eq_false_iff]
    refine ⟨⟨by simpa using hp, by simpa using hn⟩, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨⟨a,b,r⟩,hr,hd⟩ := List.any_eq_true.mp hit
    obtain ⟨z,hz,go⟩ := List.any_eq_true.mp hd
    have split := splitTwo weight ws (a,b,r) hr
    change total weight ws = weight a + weight b + total weight r at split
    have bound := subadd a b z hz
    have next : total weight (z::r) = weight z + total weight r := by simp [total]
    have no := ih (z::r) (by omega) (by omega)
    simp [no] at go

abbrev Column := Fin 4 → Bool

/-- The two oriented pairs occupy (0,1) and (2,3). A column has weight 2
if it makes both transitions in the same direction, 0 if neither moves,
and 1 otherwise. -/
def polarity (v : Column) : ℕ :=
  if v 0 = v 1 ∧ v 2 = v 3 then 0
  else if v 0 ≠ v 1 ∧ v 2 ≠ v 3 ∧ v 0 = v 2 then 2 else 1

private theorem fourRows : ∀ a b : Column,
    polarity (fun i => a i && b i) ≤ polarity a + polarity b ∧
    polarity (fun i => a i || b i) ≤ polarity a + polarity b ∧
    polarity (fun i => a i && !(b i)) ≤ polarity a + polarity b ∧
    polarity (fun i => b i && !(a i)) ≤ polarity a + polarity b := by decide +kernel

def project (rows : Fin 4 → Fin 256) (x : W) : Column :=
  fun i => x.getLsbD (rows i).val

theorem polarityLower (rows : Fin 4 → Fin 256) (d : ℕ) (ws : List W)
    (pos : total (fun x => polarity (project rows x)) ws < polarity (project rows goal))
    (neg : total (fun x => polarity (project rows x)) ws < polarity (project rows (~~~goal))) :
    optimized d 0 ws = false := by
  apply zeroSlackLower _ _ d ws pos neg
  intro a b z hz
  have ⟨h₀,h₁,h₂,h₃⟩ := fourRows (project rows a) (project rows b)
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · have eq : project rows (a &&& b) = fun i => project rows a i && project rows b i := by
      funext i
      simp [project]
    rw [eq]
    exact h₀
  · have eq : project rows (a ||| b) = fun i => project rows a i || project rows b i := by
      funext i
      simp [project]
    rw [eq]
    exact h₁
  · have eq : project rows (a &&& ~~~b) = fun i => project rows a i && !(project rows b i) := by
      funext i
      simp [project]
    rw [eq]
    exact h₂
  · have eq : project rows (b &&& ~~~a) = fun i => project rows b i && !(project rows a i) := by
      funext i
      simp [project]
    rw [eq]
    exact h₃

end Row12096Polarity
#print axioms Row12096Polarity.polarityLower
