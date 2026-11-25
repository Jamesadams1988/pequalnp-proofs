import EssentialEdges

/-! A 14-line cutting-plane derivation for the K₄ capacity inequality.
The first division obtains the {0,1,2} triangle. Doubling it and adding
the three edges incident to 3 permits division by 3 to obtain the capacity. -/
namespace CliqueEdges.Sharp
open PEqualNP.Search

private def add (a b : L) : L := (a.1+b.1,a.2+b.2)
private def mul (k : ℕ) (a : L) : L := ((k:ℤ) • a.1,(k:ℤ)*a.2)
private def cut (d : ℕ) (a : L) : L := (fun v => a.1 v / (d:ℤ), -((-a.2)/(d:ℤ)))

private def l0 : L := clauseCP (pairClause 0)
private def l1 : L := clauseCP (pairClause 1)
private def l2 : L := clauseCP (pairClause 2)
private def l3 : L := clauseCP (pairClause 3)
private def l4 : L := clauseCP (pairClause 4)
private def l5 : L := clauseCP (pairClause 5)
private def l6 : L := add l0 l1
private def l7 : L := add l6 l3
private def l8 : L := cut 2 l7
private def l9 : L := mul 2 l8
private def l10 : L := add l9 l2
private def l11 : L := add l10 l4
private def l12 : L := add l11 l5
private def l13 : L := cut 3 l12

private def bank0 : List L := []
private def bank1 := l0 :: bank0
private def bank2 := l1 :: bank1
private def bank3 := l2 :: bank2
private def bank4 := l3 :: bank3
private def bank5 := l4 :: bank4
private def bank6 := l5 :: bank5
private def bank7 := l6 :: bank6
private def bank8 := l7 :: bank7
private def bank9 := l8 :: bank8
private def bank10 := l9 :: bank9
private def bank11 := l10 :: bank10
private def bank12 := l11 :: bank11
private def bank13 := l12 :: bank12
private def bank14 := l13 :: bank13

theorem capacityInFourteen : ∃ π : List L, IsCPDerivation edges π ∧ cap ∈ π ∧ π.length = 14 := by
  have h0 : IsCPDerivation edges bank0 := .nil
  have h1 : IsCPDerivation edges bank1 := .ax (pairClause 0) h0 ⟨0, rfl⟩
  have h2 : IsCPDerivation edges bank2 := .ax (pairClause 1) h1 ⟨1, rfl⟩
  have h3 : IsCPDerivation edges bank3 := .ax (pairClause 2) h2 ⟨2, rfl⟩
  have h4 : IsCPDerivation edges bank4 := .ax (pairClause 3) h3 ⟨3, rfl⟩
  have h5 : IsCPDerivation edges bank5 := .ax (pairClause 4) h4 ⟨4, rfl⟩
  have h6 : IsCPDerivation edges bank6 := .ax (pairClause 5) h5 ⟨5, rfl⟩
  have h7 : IsCPDerivation edges bank7 := .add h6 (List.getElem_mem (l := bank6) (n := 5) (by decide)) (List.getElem_mem (l := bank6) (n := 4) (by decide))
  have h8 : IsCPDerivation edges bank8 := .add h7 (List.getElem_mem (l := bank7) (n := 0) (by decide)) (List.getElem_mem (l := bank7) (n := 3) (by decide))
  have h9 : IsCPDerivation edges bank9 := .div 2 h8 (List.getElem_mem (l := bank8) (n := 0) (by decide)) (by decide) (by decide +kernel)
  have h10 : IsCPDerivation edges bank10 := .mul 2 h9 (List.getElem_mem (l := bank9) (n := 0) (by decide))
  have h11 : IsCPDerivation edges bank11 := .add h10 (List.getElem_mem (l := bank10) (n := 0) (by decide)) (List.getElem_mem (l := bank10) (n := 7) (by decide))
  have h12 : IsCPDerivation edges bank12 := .add h11 (List.getElem_mem (l := bank11) (n := 0) (by decide)) (List.getElem_mem (l := bank11) (n := 6) (by decide))
  have h13 : IsCPDerivation edges bank13 := .add h12 (List.getElem_mem (l := bank12) (n := 0) (by decide)) (List.getElem_mem (l := bank12) (n := 6) (by decide))
  have h14 : IsCPDerivation edges bank14 := .div 3 h13 (List.getElem_mem (l := bank13) (n := 0) (by decide)) (by decide) (by decide +kernel)
  have lastLine : l13 = cap := by decide +kernel
  exact ⟨bank14,h14,lastLine ▸ (List.mem_cons_self (a := l13) (l := bank13)),rfl⟩

end CliqueEdges.Sharp
#print axioms CliqueEdges.Sharp.capacityInFourteen
