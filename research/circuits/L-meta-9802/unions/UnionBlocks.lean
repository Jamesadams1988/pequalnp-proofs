import UnionRows
namespace Row9802.Unions

def foldRows (s : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => (if s.testBit i then rows.getD i 0 else 0) ||| foldRows s i

def hood (s : Nat) : Nat := foldRows s 20

def check (lo hi : Nat) : List Nat → Bool
  | [] => true
  | s :: ss => lo ≤ hood s && hood s < hi && check (hood s + 1) hi ss

theorem check_sound (ss : List Nat) (lo hi : Nat) (h : check lo hi ss = true) :
    (ss.map hood).Pairwise (· < ·) ∧ ∀ s ∈ ss, lo ≤ hood s ∧ hood s < hi := by
  induction ss generalizing lo with
  | nil => simp
  | cons s ss ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs, hb⟩ := ih (hood s + 1) h.2
    constructor
    · simp only [List.map_cons, List.pairwise_cons, List.mem_map]
      refine ⟨?_,hs⟩
      rintro _ ⟨t,ht,rfl⟩
      exact (hb t ht).1
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact ⟨Nat.le_trans (by omega) (hb t ht).1,(hb t ht).2⟩

structure Block (lo hi n : Nat) where
  words : List Nat
  size : words.length = n
  ord : (words.map hood).Pairwise (· < ·)
  bounds : ∀ s ∈ words, lo ≤ hood s ∧ hood s < hi

def ofCheck {lo hi n : Nat} (xs : List Nat) (hn : xs.length = n) (h : check lo hi xs = true) : Block lo hi n :=
  ⟨xs,hn,(check_sound xs lo hi h).1,(check_sound xs lo hi h).2⟩

def merge {lo mid hi n m : Nat} (x : Block lo mid n) (y : Block mid hi m) (h₁ : lo ≤ mid := by decide) (h₂ : mid ≤ hi := by decide) : Block lo hi (n+m) where
  words := x.words ++ y.words
  size := by simp [x.size, y.size]
  ord := by
    rw [List.map_append, List.pairwise_append]
    refine ⟨x.ord, y.ord, ?_⟩
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    exact Nat.lt_of_lt_of_le (x.bounds u hu).2 (y.bounds v hv).1
  bounds := by
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact ⟨(x.bounds _ hs).1, Nat.lt_of_lt_of_le (x.bounds _ hs).2 h₂⟩
    · exact ⟨Nat.le_trans h₁ (y.bounds _ hs).1, (y.bounds _ hs).2⟩
end Row9802.Unions
