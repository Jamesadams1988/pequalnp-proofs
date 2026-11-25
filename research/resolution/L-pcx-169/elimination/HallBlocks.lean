import HallLocal

namespace Row169.HallLocal

open PEqualNP.ProofComplexity

abbrev P := Fin 5
abbrev H := Fin 4
abbrev Cell := P × H
abbrev C := Clause Cell

inductive Key where
  | row
  | prior (h : H)
  | clash (i : P) (h : H)
  deriving DecidableEq

def holes (mask : Nat) := (List.finRange 4).filter fun h => mask.testBit h.val

def old (k : P) := (List.finRange 5).filter fun i => i < k

def keys (k : P) (mask : Nat) : List Key :=
  [.row] ++ (holes mask).map .prior ++
    (old k).flatMap (fun i => (holes mask).map (Key.clash i))

def positives (f : Cell → Bool) : C :=
  (Finset.univ.filter (fun v : Cell => f v = true)).image (fun v => (v,true))

def target (k : P) (mask : Nat) : C :=
  positives (fun (i,h) => decide (i ≤ k) && !mask.testBit h.val)

def source (k : P) (mask : Nat) : Key → C
  | .row => positives (fun (i,_) => i == k)
  | .prior b => positives (fun (i,h) => decide (i < k) && (!mask.testBit h.val || h == b))
  | .clash i h => {((i,h),false),((k,h),false)}

def stock (k : P) (mask : Nat) : Finset C :=
  ((keys k mask).map (source k mask)).toFinset

def witness (k : P) (mask : Nat) (s : Key) (v : Cell) : Bool :=
  mask.testBit v.2.val && match s with
    | .row => decide (v.1 < k)
    | .prior h => (v.1 == k && v.2 == h) || (decide (v.1 < k) && v.2 != h)
    | .clash i h => (v.1 == k && v.2 == h) ||
        (decide (v.1 < k) && (v.2 != h || v.1 == i))

private instance (a : Cell → Bool) (c : C) : Decidable (ClauseSat a c) := by
  unfold ClauseSat
  infer_instance

def check (k : P) (mask : Nat) : Bool :=
  let ks := keys k mask
  ks.all fun x =>
    !(decide (ClauseSat (witness k mask x) (target k mask))) &&
      ks.all (fun y => (x == y) || decide (ClauseSat (witness k mask x) (source k mask y)))

theorem localBound {k : P} {mask n : Nat} {π}
    (ok : check k mask = true)
    (card : (stock k mask).card = 1 + k.val + k.val^2)
    (built : Joined (stock k mask) n π) (ht : target k mask ∈ π) : k.val + k.val^2 ≤ n := by
  have required := joinsNeededOfModels (stock := stock k mask) (target := target k mask) ?_ built ht
  · omega
  intro c hc
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
  refine ⟨witness k mask x, ?_, ?_⟩
  · have pass := List.all_eq_true.mp ok x hx
    simpa using (Bool.and_eq_true_iff.mp pass).1
  · intro d hd bad
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    have pass := List.all_eq_true.mp ok x hx
    have item := List.all_eq_true.mp (Bool.and_eq_true_iff.mp pass).2 y hy
    have eq : x = y := by simpa [bad] using item
    rw [eq]

/-- Check just the nonempty local blocks of the five-pigeon proof. -/
def blocks : List (P × Nat) :=
  (List.range 16).filterMap fun mask =>
    let n := (holes mask).length
    if h : 0 < n ∧ n < 5 then some (⟨n,h.2⟩,mask) else none

def checked (s : P × Nat) : Bool :=
  check s.1 s.2 && decide ((stock s.1 s.2).card = 1 + s.1.val + s.1.val^2)

set_option maxRecDepth 10000 in
theorem verified : blocks.all checked = true := by decide +kernel

theorem eachBlock {k : P} {mask n : Nat} {π} (hb : (k,mask) ∈ blocks)
    (built : Joined (stock k mask) n π) (ht : target k mask ∈ π) : k.val + k.val^2 ≤ n := by
  have pass := Bool.and_eq_true_iff.mp (List.all_eq_true.mp verified (k,mask) hb)
  exact localBound pass.1 (of_decide_eq_true pass.2) built ht

theorem totalJoins : (blocks.map (fun (k,_) => k.val + k.val^2)).sum = 112 := by decide +kernel

#print axioms eachBlock
#print axioms totalJoins

end Row169.HallLocal
