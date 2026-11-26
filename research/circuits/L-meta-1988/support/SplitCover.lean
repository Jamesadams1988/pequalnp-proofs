import Mathlib

namespace ProjectivePlaneSplitCover

abbrev Vertex := Fin 26
abbrev Assignment := Vertex → Bool
abbrev Function := Assignment → Bool

/-- Read-once positive formulas whose raw input variables are contained in the scope. -/
inductive ReadOnce : Finset Vertex → Function → Prop
  | constant (b : Bool) : ReadOnce ∅ (fun _ => b)
  | variable (v : Vertex) : ReadOnce {v} (fun x => x v)
  | andGate {s t f g} : Disjoint s t → ReadOnce s f → ReadOnce t g →
      ReadOnce (s ∪ t) (fun x => f x && g x)
  | orGate {s t f g} : Disjoint s t → ReadOnce s f → ReadOnce t g →
      ReadOnce (s ∪ t) (fun x => f x || g x)
  | enlarge {s t f} : s ⊆ t → ReadOnce s f → ReadOnce t f

/-- Certificate produced recursively by taking an earliest shared wire,
isolating its read-once cone, and substituting the two constant values. -/
inductive Split : Finset Vertex → Function → ℕ → Prop
  | leaf {s f} : ReadOnce s f → Split s f 0
  | pad {s f k} : Split s f k → Split s f (k + 1)
  | branch {s t g lo hi k} : Disjoint s t → ReadOnce s g → Split t lo k → Split t hi k →
      Split (s ∪ t) (fun x => hi x && (g x || lo x)) (k + 1)

def Covered (s : Finset Vertex) (f : Function) (n : ℕ) : Prop :=
  ∃ fs : List Function, fs.length ≤ n ∧ (∀ q ∈ fs, ReadOnce s q) ∧
    ∀ x, fs.all (fun q => q x) = f x

private theorem distribute (fs : List Function) (g : Function) (x : Assignment) :
    (fs.map (fun q y => g y || q y)).all (fun q => q x) =
      (g x || fs.all (fun q => q x)) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.all_cons] at *
    rw [ih]
    cases g x <;> simp

theorem split_cover {s f k} (proof : Split s f k) : Covered s f (2 ^ k) := by
  induction proof with
  | @leaf s f ro =>
    refine ⟨[f], by simp, ?_, by simp⟩
    simpa using ro
  | pad _ ih =>
    obtain ⟨fs, bound, valid, exactOn⟩ := ih
    exact ⟨fs, bound.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)), valid, exactOn⟩
  | @branch s t g lo hi k disjoint guard _ _ lowCover highCover =>
    obtain ⟨low, lowBound, lowValid, lowExact⟩ := lowCover
    obtain ⟨high, highBound, highValid, highExact⟩ := highCover
    refine ⟨high ++ low.map (fun q y => g y || q y), ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, pow_succ]
      omega
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact ReadOnce.enlarge Finset.subset_union_right (highValid _ hq)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        exact ReadOnce.orGate disjoint guard (lowValid _ hr)
    · intro x
      rw [List.all_append, highExact, distribute, lowExact]

/-- Monotone Shannon expansion uses this identity even if the designated wire
originally occurs more than twice. -/
theorem monotone_split (g lo hi : Bool) (monotone : lo = true → hi = true) :
    (if g then hi else lo) = (hi && (g || lo)) := by
  cases g <;> cases lo <;> cases hi <;> simp_all

#print axioms split_cover
#print axioms monotone_split

end ProjectivePlaneSplitCover
