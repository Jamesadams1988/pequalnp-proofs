import ColumnCatalog

/-! A positive-coefficient representation of the four-variable inequalities
a*x0 + b*x1 + c*x2 + d*x3 ≤ rhs. The bit mask records which of the six
pairwise collision axioms a tree consumes. -/
namespace K4Column

def add (u v : Line) : Line :=
  ⟨u.a+v.a,u.b+v.b,u.c+v.c,u.d+v.d,u.rhs+v.rhs⟩

def divide (u : Line) (k : ℕ) : Line :=
  ⟨u.a/k,u.b/k,u.c/k,u.d/k,u.rhs/k⟩

def divisible (u : Line) (k : ℕ) : Prop :=
  k ∣ u.a ∧ k ∣ u.b ∧ k ∣ u.c ∧ k ∣ u.d

instance (u : Line) (k : ℕ) : Decidable (divisible u k) := by
  unfold divisible
  infer_instance

def edge : Fin 6 → ℕ × Line := ![
  (1,⟨1,1,0,0,1⟩), (2,⟨1,0,1,0,1⟩), (4,⟨1,0,0,1,1⟩),
  (8,⟨0,1,1,0,1⟩), (16,⟨0,1,0,1,1⟩), (32,⟨0,0,1,1,1⟩)]

/-- Addition combines disjoint sets of input edges. Division may be nested
to arbitrary depth, with any positive divisor that divides every coefficient. -/
inductive ReadOnce : ℕ × Line → Prop
  | leaf (e : Fin 6) : ReadOnce (edge e)
  | join {p q} : ReadOnce p → ReadOnce q → p.1 &&& q.1 = 0 →
    ReadOnce (p.1 ||| q.1, add p.2 q.2)
  | cut {p} (k : ℕ) : ReadOnce p → 0 < k → divisible p.2 k →
    ReadOnce (p.1, divide p.2 k)

theorem leaves_checked : ∀ e : Fin 6, edge e ∈ catalog := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sums_checked : ∀ p ∈ catalog, ∀ q ∈ catalog, p.1 &&& q.1 = 0 →
    (p.1 ||| q.1, add p.2 q.2) ∈ catalog := by decide +kernel

set_option maxRecDepth 20000 in
theorem cuts_checked : ∀ p ∈ catalog, ∀ k : Fin 4, 0 < k.val → divisible p.2 k.val →
    (p.1, divide p.2 k.val) ∈ catalog := by decide +kernel

set_option maxRecDepth 20000 in
theorem has_small_coeff : ∀ p ∈ catalog,
    (0 < p.2.a ∧ p.2.a ≤ 3) ∨ (0 < p.2.b ∧ p.2.b ≤ 3) ∨
    (0 < p.2.c ∧ p.2.c ≤ 3) ∨ (0 < p.2.d ∧ p.2.d ≤ 3) := by decide +kernel

theorem in_catalog {p} (h : ReadOnce p) : p ∈ catalog := by
  induction h with
  | leaf e => exact leaves_checked e
  | join _ _ disjoint ih jh => exact sums_checked _ ih _ jh disjoint
  | @cut p k _ pos divides ih =>
    obtain ⟨da,db,dc,dd⟩ := divides
    have hk : k ≤ 3 := by
      rcases has_small_coeff p ih with ha | hb | hc | hd
      · exact (Nat.le_of_dvd ha.1 da).trans ha.2
      · exact (Nat.le_of_dvd hb.1 db).trans hb.2
      · exact (Nat.le_of_dvd hc.1 dc).trans hc.2
      · exact (Nat.le_of_dvd hd.1 dd).trans hd.2
    exact cuts_checked p ih ⟨k, by omega⟩ pos ⟨da,db,dc,dd⟩

set_option maxRecDepth 20000 in
theorem cap_absent : ∀ p ∈ catalog, p.2 ≠ ⟨1,1,1,1,1⟩ := by decide +kernel

theorem noReadOnceCapacity (s : ℕ) : ¬ ReadOnce (s, ⟨1,1,1,1,1⟩) :=
  fun h => cap_absent _ (in_catalog h) rfl

end K4Column
#print axioms K4Column.noReadOnceCapacity
