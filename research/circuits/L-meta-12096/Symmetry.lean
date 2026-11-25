import SignedFrontier

/-!
The six input columns split into orbits {0,1,2}, {3}, and {4,5}. All twelve
permutations of those blocks act on the 128 ordered pairs of assignments in
the signed frontier. The action is applied to both 128-bit halves of a wire.
The input, goal, inverse, branch, and orbit certificates below are checked by
kernel reduction. Representative subtree exclusions remain hypotheses.
-/

namespace Row12096Signed.Symmetry
open Row12096Signed

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Entry g packs 128 consecutive seven-bit destination indices, least significant first.
Each row of inputData specifies which input wire is the image of a given input. -/
private def pairData : Array Nat := #[0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080,
  0xfff7f7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7a7568cf9a03f7cf5e3b74e1bb672d5a3364c582f5cb15aa5aa54274c952234280fa23c74e65c98f161c17eddebb72d59b15eb55a94e7d2a34274d992e54991123c68b0e1413668c982e54b1426488901e3860d16284880e182830808080,
  0xfffbefcf5efcf8efcf971edd7a70dfbb6ebd9ab4e7d19b2e4af5aad3a94a8d09f3674cc78b0dfc17aedcb766d58972a4498f1a2c4850e0c07ec98b05cbd6ac56a94294ef9ebc74edcb86ed9a3566992a348890a03e74f1c3668c973058a9328484070a182030404011203878d182c509,
  0xfff7f7cf5efcf8efcf971edd7a70dfbb6ebd9a7567d19a03f64c582e5eb15aa5aa14a77cf5e3a76e1bb672d1ab34c951a44280fa23a78e65c95eb55a7527d2a3426ce998f161bf82ddebb72cdab12e54893123c68b0a1c13668c973054b1328484070a181840404011203878c1a2c509,
  0xfffbefcf7e7d78eddfaf4e7c37f2e3bb66dd7ab4e8cd9f2e3c98b061bf7aedcb76ac59af2e4ca911e345890e0c2ad52ad3a54684f9d326c07cfdebb78e9cb86ed9ab368c93244a8d121407cf1c3ac57b05cb562b54a53a836447901c3460b1424d18325cb15284c9080c1c2840604100,
  0xfff7f7cf7e7d78eddfaf4e7c37f2e3bb66dd7a7568cd9e03e7ef5dbc74e1bb672d59b46499225468501f4478e1d62bd82e58ad52d529d465c793160c37eddebb72d58b35e5c995222478d161c1855aa55a73e951a13a64d36447901c3068b1424d18325ca96284c9080c1c2830804100,
  0xfffbefcf5e7df8e7df971edc37f5e9bb5edd9ab4e7cda32d7c95a9d5a94a8d09f3664ec72e44a931e345890a0c3c57f0e0bd76e5bb362d4064fd8ae60bd6ac56a942752f93234a91121407ce9c3cf5d3c76e5c376cd19b536202870c101820200d173260b1526509111c4078d1828589,
  0xfff7f7cf5e7df8e7df971edc37f5e9bb5edd9a7567cda20327ec57305eb15aa5aa13a97c991a5488501f4474e1e7ae9e3b70ddb3968cdae5af92b53ab527d2a3426cc9d8e5c895262478d16141878afe1c16ef5db966c5a36202870c0c2020200d173260a9626509111c4078c1a28589,
  0xfffbefcf3efd78edcf86fefd7a72e3bb66bdbab4e6d19f2e3af2e4c8951e34589061c2c98b05fc37aedcb762d59ad529d5a54684f993a6c07cc93244695121407ce1e3afdebb74f1cb86ed99b568c57ae60b562b549d4a8364478e203460a16244060a1c203020801a305cc962a50992,
  0xfff7f7cf3efd78edcf86fefd7a72e3bb66bdba7566d19e03e64992234a8501f4470f1d7ef5dba78e1bb672cdab462bd73058ad52d4ea5465c75e5c9912a2478d160c38593160bf86ddebb72c5ab35aa53ab3e951a13274d364478e203068a16244060a1c184020801a305cc952c50992,
  0xfffbefcf3ebdf8e7db86fefcb8f5e9bb5ecdbab4e6cfa32d7c72e449951e3458906143c95a9d4ab4a8d09f326cec57f061bd76e5bb166d4064f93234895121407ce1d3cfd8ae5ec16ac56a93a852f5d3b78e5c376ccda3536202860e10181040088e1e4068c142c49a2e60c962a4ca12,
  0xfff7f7cf3ebdf8e7db86fefcb8f5e9bb5ecdba7566cfa20327c991a44a8501f4470e9e7ec572f60b15aa5a9d4297ae9dbc70ddb3966d1ae5af8e5c8932a2478d160c28792b53a9567d2a34264d9d8afe0c36ef5db962cda36202860e0c201040088e1e4060d142c49a2e60c952c4ca12]
private def inputData : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 5, 4], #[0, 2, 1, 3, 4, 5], #[0, 2, 1, 3, 5, 4], #[1, 0, 2, 3, 4, 5], #[1, 0, 2, 3, 5, 4], #[1, 2, 0, 3, 4, 5], #[1, 2, 0, 3, 5, 4], #[2, 0, 1, 3, 4, 5], #[2, 0, 1, 3, 5, 4], #[2, 1, 0, 3, 4, 5], #[2, 1, 0, 3, 5, 4]]
private def inverseData : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 9, 6, 7, 10, 11]

def lane (g : Fin 12) (k : Fin 256) : Fin 256 :=
  let j := ((pairData.getD g.val 0) >>> (7 * (k.val % 128))) % 128
  Fin.ofNat 256 (j + (k.val / 128) * 128)
def pi (g : Fin 12) (i : Fin 6) : Fin 6 :=
  Fin.ofNat 6 ((inputData[g.val]!).getD i.val 0)
def inverse (g : Fin 12) : Fin 12 := Fin.ofNat 12 (inverseData.getD g.val 0)
def input (i : Fin 6) : W := xs.getD i.val 0

/-- Pull back the 256 coordinates of a word along a permutation of the labelled pairs. -/
def pull (g : Fin 12) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k : Fin 256 => w[(lane g k).val])).cast (by simp)

@[simp] theorem pull_bit (g : Fin 12) (w : W) (k : Fin 256) :
    (pull g w)[k.val] = w[(lane g k).val] := by
  change (pull g w).getLsbD k.val = _
  simp only [pull, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left k.isLt, Option.getD_some]

@[simp] theorem pull_get (g : Fin 12) (w : W) (i : ℕ) (hi : i < 256) :
    (pull g w)[i] = w[(lane g ⟨i, hi⟩).val] := pull_bit g w ⟨i,hi⟩

theorem lane_inverse : ∀ (g : Fin 12) (k : Fin 256), lane g (lane (inverse g) k) = k := by
  decide +kernel

theorem pull_injective (g : Fin 12) : Function.Injective (pull g) := by
  intro a b h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let k : Fin 256 := ⟨i, hi⟩
  have eq := congrArg (fun x : W => x[(lane (inverse g) k).val]) h
  simpa only [pull_bit, lane_inverse] using eq

@[simp] theorem pull_and (g : Fin 12) (a b : W) : pull g (a &&& b) = pull g a &&& pull g b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (pull g (a &&& b))[(⟨i,hi⟩ : Fin 256).val] = (pull g a &&& pull g b)[(⟨i,hi⟩ : Fin 256).val]
  simp only [pull_get, BitVec.getElem_and]
@[simp] theorem pull_or (g : Fin 12) (a b : W) : pull g (a ||| b) = pull g a ||| pull g b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (pull g (a ||| b))[(⟨i,hi⟩ : Fin 256).val] = (pull g a ||| pull g b)[(⟨i,hi⟩ : Fin 256).val]
  simp only [pull_get, BitVec.getElem_or]
@[simp] theorem pull_not (g : Fin 12) (a : W) : pull g (~~~a) = ~~~(pull g a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (pull g (~~~a))[(⟨i,hi⟩ : Fin 256).val] = (~~~(pull g a))[(⟨i,hi⟩ : Fin 256).val]
  simp only [pull_get, BitVec.getElem_not]

private theorem goalBits : ∀ (g : Fin 12) (k : Fin 256), goal[(lane g k).val] = goal[k.val] := by
  decide +kernel
@[simp] theorem pull_goal (g : Fin 12) : pull g goal = goal := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  exact (pull_bit g goal ⟨i,hi⟩).trans (goalBits g ⟨i,hi⟩)

private theorem inputBits : ∀ (g : Fin 12) (i : Fin 6) (k : Fin 256),
    (input i)[(lane g k).val] = (input (pi g i))[k.val] := by decide +kernel

@[simp] theorem pull_input (g : Fin 12) (i : Fin 6) : pull g (input i) = input (pi g i) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  exact (pull_bit g (input i) ⟨j,hj⟩).trans (inputBits g i ⟨j,hj⟩)

theorem live_image {α β : Type} [DecidableEq α] [DecidableEq β]
    {o : α → α → Finset α} {p : β → β → Finset β} (f : α → β)
    (inj : Function.Injective f) (op : ∀ a b z, z ∈ o a b → f z ∈ p (f a) (f b))
    {g : α} {n : ℕ} {s : Finset α} (h : live o g n s) : live p (f g) n (s.image f) := by
  induction n generalizing s with
  | zero => change s = {g} at h; simp [h, live]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, ne, z, hz, newZ, rest, hr, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem _ ha, f b, Finset.mem_image_of_mem _ hb,
        fun eq => ne (inj eq), f z, op _ _ _ hz, ?_, rest.image f, ?_, ?_⟩
      · simpa [Finset.mem_image, inj.eq_iff] using newZ
      · simp [hr]
      · simpa using ih tail

theorem pull_ops (g : Fin 12) (a b z : W) (h : z ∈ basicOps a b) :
    pull g z ∈ basicOps (pull g a) (pull g b) := by
  simp [basicOps, ops] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

end Row12096Signed.Symmetry

namespace Row12096Signed.Symmetry
open Row12096Signed

set_option maxRecDepth 12000
set_option maxHeartbeats 0

def wordGate (a b : W) : ℕ → W
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

theorem pull_gate (g : Fin 12) (a b : W) (o : ℕ) :
    pull g (wordGate a b o) = wordGate (pull g a) (pull g b) o := by
  unfold wordGate
  split <;> simp

def inputs : Finset W := Finset.univ.image input

private theorem permutesInputs : ∀ g : Fin 12, (Finset.univ.image fun i => input (pi g i)) = inputs := by
  decide +kernel
theorem pull_inputs (g : Fin 12) : inputs.image (pull g) = inputs := by
  rw [inputs, Finset.image_image]
  simpa only [inputs, Function.comp_def, pull_input] using permutesInputs g

def headAt (i : Fin 60) : State := heads.getD i.val first
/-- Each root code specifies two input indices and the donor's operation index. -/
private def indexCodes : Array (Fin 6 × Fin 6 × ℕ) := #[(0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3), (0, 2, 0), (0, 2, 1), (0, 2, 2), (0, 2, 3), (0, 3, 0), (0, 3, 1), (0, 3, 2), (0, 3, 3), (0, 4, 0), (0, 4, 1), (0, 4, 2), (0, 4, 3), (0, 5, 0), (0, 5, 1), (0, 5, 2), (0, 5, 3), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 3, 0), (1, 3, 1), (1, 3, 2), (1, 3, 3), (1, 4, 0), (1, 4, 1), (1, 4, 2), (1, 4, 3), (1, 5, 0), (1, 5, 1), (1, 5, 2), (1, 5, 3), (2, 3, 0), (2, 3, 1), (2, 3, 2), (2, 3, 3), (2, 4, 0), (2, 4, 1), (2, 4, 2), (2, 4, 3), (2, 5, 0), (2, 5, 1), (2, 5, 2), (2, 5, 3), (3, 4, 0), (3, 4, 1), (3, 4, 2), (3, 4, 3), (3, 5, 0), (3, 5, 1), (3, 5, 2), (3, 5, 3), (4, 5, 0), (4, 5, 1), (4, 5, 2), (4, 5, 3)]
private def repData : Array (Fin 60) := #[0, 1, 2, 2, 0, 1, 2, 2, 8, 9, 10, 11, 12, 13, 14, 15, 12, 13, 14, 15, 0, 1, 2, 2, 8, 9, 10, 11, 12, 13, 14, 15, 12, 13, 14, 15, 8, 9, 10, 11, 12, 13, 14, 15, 12, 13, 14, 15, 48, 49, 50, 51, 48, 49, 50, 51, 56, 57, 58, 58]
private def moveData : Array (Fin 12) := #[0, 0, 0, 4, 2, 2, 2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 8, 8, 8, 10, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1]
def repIds : List (Fin 60) := [0, 1, 2, 8, 9, 10, 11, 12, 13, 14, 15, 48, 49, 50, 51, 56, 57, 58]
def repId (i : Fin 60) : Fin 60 := repData.getD i.val 0
def moveId (i : Fin 60) : Fin 12 := moveData.getD i.val 0
def coordinates (i : Fin 60) : Fin 6 × Fin 6 × ℕ := indexCodes.getD i.val (0,0,0)
def newWord (i : Fin 60) := let c := coordinates i; wordGate (input c.1) (input c.2.1) c.2.2
/-- Minimum zero-based head index in each of the eighteen orbits. -/
def representatives : List State := repIds.map headAt

private theorem movedGate : ∀ i : Fin 60, let c := coordinates i; let g := moveId i
    wordGate (input (pi g c.1)) (input (pi g c.2.1)) c.2.2 = newWord (repId i) := by decide +kernel

private theorem headSet : ∀ i : Fin 60, (headAt i).2.toFinset = insert (newWord i) inputs := by
  decide +kernel

theorem moveHead (i : Fin 60) : (headAt i).2.toFinset.image (pull (moveId i)) =
    (headAt (repId i)).2.toFinset := by
  rw [headSet, headSet, Finset.image_insert, pull_inputs]
  congr 1
  simpa only [newWord, pull_gate, pull_input] using movedGate i

private theorem headFacts : ∀ i : Fin 60, repId i ∈ repIds ∧ (headAt i).2.Nodup ∧
    (headAt i).1 + (headAt i).2.length = 11 := by decide +kernel

theorem representativeCount : representatives.length = 18 ∧ representatives.Nodup ∧ heads.length = 60 := by
  decide +kernel

/-- Every live signed run at a root child transports to its designated orbit representative. -/
theorem representativeLive {t : W} (ht : t = goal ∨ t = ~~~goal) (k : ℕ) (i : Fin 60)
    (h : live basicOps t k (headAt i).2.toFinset) :
    live basicOps t k (headAt (repId i)).2.toFinset := by
  have m := live_image _ (pull_injective (moveId i)) (pull_ops (moveId i)) h
  rw [moveHead] at m
  rcases ht with rfl | rfl <;> simpa using m

theorem rejectLiveHeads (reject : ∀ p ∈ representatives, optimized 10 p.1 p.2 = false)
    {t : W} (ht : t = goal ∨ t = ~~~goal) {p : State} (hp : p ∈ heads) :
    ¬ live basicOps t 10 p.2.toFinset := by
  have allH : heads = List.ofFn headAt := by decide +kernel
  rw [allH, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  intro h
  have facts := headFacts (repId i)
  have ok := optimized_complete ht 10 _ _ facts.2.1 facts.2.2 (representativeLive ht 10 i h)
  have bad := reject (headAt (repId i)) (List.mem_map.mpr ⟨repId i, (headFacts i).1, rfl⟩)
  exact Bool.noConfusion (bad.symm.trans ok)

end Row12096Signed.Symmetry

namespace Row12096Signed.Symmetry
open Row12096Signed

/-- A genuine live run contradicts any claimed first layer whose covered children are all dead. -/
theorem rejectLiveLayer {g : W} (hg : g = goal ∨ g = ~~~goal) {k e : ℕ}
    {ws : List W} {states : List State} (hn : ws.Nodup) (room : e + ws.length = k+2)
    (covered : nextLayer (outsideList states) e ws = false)
    (dead : ∀ p ∈ states, ¬ live basicOps g k p.2.toFinset) :
    ¬ live basicOps g (k+1) ws.toFinset := by
  intro h
  suffices nextLayer (outsideList states) e ws = true from Bool.noConfusion (covered.symm.trans this)
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · rcases hg with rfl | rfl <;> simp [nextLayer, singleton_list hn done]
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        dispatch e (outsideList states) a b r = true := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        exact hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have len := perm.length_eq
      simp only [List.length_cons] at len
      apply dispatch_complete (k := k) (extra := e) _ hop hk (by omega) (by omega) (cuts_full hg hl)
      have miss : (k-kept.length, z :: kept) ∉ states := fun hm => dead _ hm hl
      simpa [outsideList] using miss
    simp only [nextLayer, Bool.or_eq_true, List.any_eq_true]
    right
    rcases hm with direct | swap
    · exact ⟨(a,b,r), direct, go hp hs hz⟩
    · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

set_option maxRecDepth 12000 in
theorem noSignedBuild (reject : ∀ p ∈ representatives, optimized 10 p.1 p.2 = false)
    {t : W} (ht : t = goal ∨ t = ~~~goal) : ¬ build basicOps t 11 xs.toFinset := by
  intro h
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := xs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hl' : live basicOps t 11 ws.toFinset := eq.symm ▸ hl
  have hcuts := cuts_full ht hl'
  have cover : xs.sublists.all (fun v => !(cuts v == -1) || v == xs) = true := by decide +kernel
  have mem : ws ∈ xs.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have allW := List.all_eq_true.mp cover _ mem
  have eqw : ws = xs := by simpa [hcuts] using allW
  rw [eqw] at hl'
  exact rejectLiveLayer (k := 10) (e := 6) ht (by decide +kernel) (by decide +kernel)
    rootCoverage (fun _ hp => rejectLiveHeads reject ht hp) hl'



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000
set_option maxHeartbeats 0
private def bit (k : Fin 256) (w : W) : Bool := w[k.val]

theorem binaryBound18 (reject : ∀ p ∈ representatives, optimized 10 p.1 p.2 = false)
    (C : Circuit) (hg : ∀ g ∈ C.gates, legal g)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target12096 x) :
    11 < binaryCost C.gates := by
  by_contra! low
  have init : ∀ u ∈ xs, holds xs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) : C.eval (xs.map (bit k)) = bit k goal := by
    let x (i : Fin 6) : Bool := bit k (xs.getD i.val 0)
    have same : List.ofFn x = xs.map (bit k) := by
      apply List.ext_getElem
      · simp [xs]
      · intro i hi hj
        have hlt : i < xs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change C.eval (xs.map (bit k)) = bit k goal
    rw [← same, he]
    exact sampleRows k
  obtain ⟨t, ht, run⟩ := compile C.gates C.output hg xs xs.toFinset init evaluate
  have lift {a b : ℕ} (hab : a ≤ b) (hr : build basicOps t a xs.toFinset) :
      build basicOps t b xs.toFinset := by
    induction hab with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact noSignedBuild reject ht (lift low run)

theorem replacement18 (remaining : ∀ p ∈ representatives, optimized 10 p.1 p.2 = false)
    (witness13 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧ ∀ x, C.eval (List.ofFn x) = target12096 x)
    (s : ℕ) (h : HasCircuitSize 6 target12096 s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target12096 x := by
  obtain ⟨C,ok,size,ev⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,mem,op⟩ := hn
    have short : binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, mem, by simp [isBinary, op]⟩
    have lb := binaryBound18 remaining C ok ev
    obtain ⟨D,hm,hs,hd⟩ := witness13
    exact ⟨D,hm,by omega,hd⟩
  · refine ⟨C,?_,size,ev⟩
    intro g mem
    obtain ⟨hop,har⟩ := ok g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn ⟨g,mem,e⟩).elim)),har⟩

#print axioms replacement18
end Row12096Signed.Symmetry
