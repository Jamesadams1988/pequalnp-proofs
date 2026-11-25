import ForestBridge
import PEqualNP.Outside.L_meta_4795

namespace SmallIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open ForestIncidence
open PEqualNP.Outside.L_meta_4795_aux (relabel_size conj_38)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cycleI (π : Fin 3 → Fin 3) (p l : Fin 3) : Prop := π p ≠ l
instance (π : Fin 3 → Fin 3) : DecidableRel (cycleI π) := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))
instance (π : Fin 3 → Fin 3) (x : Fin 6 → Bool) : Decidable (incidence (cycleI π) x) := by
  unfold incidence
  infer_instance

def wireMap (π : Fin 3 → Fin 3) (i : Fin 6) : Fin 6 :=
  let base : Fin 6 → Fin 6 := ![0,3,4,5,2,1]
  if h : i.val < 3 then base ⟨(π ⟨i.val,h⟩).val, by omega⟩ else base i

def conj38Fn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
    (x 3 && x 5) || (x 4 && x 5)

private theorem lowerMap :
    ∀ π : Fin 3 → Fin 3, Function.Injective π → ∀ x : Fin 6 → Bool,
    decide (incidence (cycleI π) (x ∘ wireMap π)) = conj38Fn x := by decide +kernel

theorem cycle_lower (π : Fin 3 → Fin 3) (hπ : Function.Injective π) (C : Circuit)
    (hc : Monotone2 C) (hf : ∀ z, circuitFun 6 C z = true ↔ incidence (cycleI π) z) :
    8 ≤ C.size := by
  have hcs : HasCircuitSize 6 (fun x => decide (incidence (cycleI π) x)) C.size := by
    refine ⟨C,?_,le_rfl,?_⟩
    · intro g hg
      obtain ⟨hop,hl⟩ := hc g hg
      refine ⟨?_,hl⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
      exact hop.imp_right Or.inl
    · intro x
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq, circuitFun] using hf x
  have h := relabel_size (wireMap π) _ _ hcs
  have he : (fun x : Fin 6 → Bool => decide (incidence (cycleI π) (x ∘ wireMap π))) = conj38Fn :=
    funext (lowerMap π hπ)
  rw [he] at h
  exact conj_38 _ h

def starCircuit (π : Fin 3 → Fin 3) : Circuit :=
  let a (i : Fin 3) := 3 + ((π i).val+1)%3
  let b (i : Fin 3) := 3 + ((π i).val+2)%3
  ⟨[⟨.or,[a 0,b 0]⟩, ⟨.and,[0,6]⟩, ⟨.or,[a 1,b 1]⟩, ⟨.and,[1,8]⟩,
    ⟨.or,[a 2,b 2]⟩, ⟨.and,[2,10]⟩, ⟨.or,[7,9]⟩, ⟨.or,[12,11]⟩],13⟩

private theorem star_mono (π) : Monotone2 (starCircuit π) := by
  intro g hg
  simp only [starCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

private theorem star_back : ∀ π : Fin 3 → Fin 3, ∀ j : Fin 8,
    ∀ w ∈ (gateAt (starCircuit π) j).inputs, w < 6+j := by decide +kernel

private theorem star_correct : ∀ π : Fin 3 → Fin 3, ∀ z : Fin 6 → Bool,
    circuitFun 6 (starCircuit π) z = true ↔ incidence (cycleI π) z := by decide +kernel

local instance (op : GateOp) : Decidable (op = GateOp.and) := by
  cases op <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

private theorem star_productive : ∀ π : Fin 3 → Fin 3, ∀ j : Fin 8,
    (gateAt (starCircuit π) j).op = .and → ∀ z : Fin 6 → Bool,
    ((starCircuit π).wires (List.ofFn z)).getD (6+j) false = true → incidence (cycleI π) z := by decide +kernel

private theorem star_zero : ∀ π : Fin 3 → Fin 3, ∀ j : Fin 8,
    (gateAt (starCircuit π) j).op = .and → ∀ v : Fin 6,
    ((starCircuit π).wires (List.ofFn (fun k : Fin 6 => decide (k=v)))).getD (6+j) false = false := by decide +kernel

theorem cycle_normalization (π : Fin 3 → Fin 3) (hπ : Function.Injective π) (C : Circuit)
    (hc : Monotone2 C) (hf : ∀ z, circuitFun 6 C z = true ↔ incidence (cycleI π) z) :
    ∃ D, Normal (cycleI π) C D := by
  refine ⟨starCircuit π,star_mono π,?_,cycle_lower π hπ C hc hf,star_correct π,?_,?_⟩
  · intro j hj
    exact star_back π ⟨j,hj⟩
  · intro j hj h z hz
    exact Or.inr (Or.inr (star_productive π ⟨j,hj⟩ h z hz))
  · intro j hj h
    exact ⟨fun p => star_zero π ⟨j,hj⟩ h _,fun l => star_zero π ⟨j,hj⟩ h _⟩

#print axioms cycle_normalization
end SmallIncidence
