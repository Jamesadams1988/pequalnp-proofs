import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9682.Certificate
open PEqualNP.ProofComplexity PEqualNP.Search

abbrev V := Fin 4 × Fin 3
abbrev L := CPLine V
abbrev F := PHP 4 3

def pigeon (p : Fin 4) := Finset.univ.image (fun h : Fin 3 => ((p, h), true))
def pair (h : Fin 3) (p q : Fin 4) : Clause V := {((p, h), false), ((q, h), false)}

theorem pigeonMem (p : Fin 4) : pigeon p ∈ F := Or.inl ⟨p, rfl⟩
theorem pairMem (h : Fin 3) (p q : Fin 4) (ne : p ≠ q) : pair h p q ∈ F :=
  Or.inr ⟨p, q, h, ne, rfl⟩

def dataLine (coeffs : List ℤ) (rhs : ℤ) : L :=
  (fun v => coeffs.getD (3 * v.1.val + v.2.val) 0, rhs)

theorem recode {π : List L} {a b : L} (prev : IsCPDerivation F (a :: π))
    (hf : ∀ v, a.1 v = b.1 v) (hc : a.2 = b.2) : IsCPDerivation F (b :: π) := by
  have eq : a = b := Prod.ext (funext hf) hc
  rwa [← eq]

theorem earlier (xs : List L) (k : ℕ) (hk : k < xs.length) : xs[k] ∈ xs :=
  List.getElem_mem hk

def empty : List L := []
theorem start : IsCPDerivation F empty := .nil

def line0 : L := dataLine [-1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history0 : List L := line0 :: empty
theorem sound0 : IsCPDerivation F history0 :=
  recode (IsCPDerivation.ax (pair 0 0 1) start (pairMem 0 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line1 : L := dataLine [-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history1 : List L := line1 :: history0
theorem sound1 : IsCPDerivation F history1 :=
  recode (IsCPDerivation.ax (pair 0 0 2) sound0 (pairMem 0 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line2 : L := dataLine [0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history2 : List L := line2 :: history1
theorem sound2 : IsCPDerivation F history2 :=
  recode (IsCPDerivation.ax (pair 0 1 2) sound1 (pairMem 0 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line3 : L := dataLine [-2, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0] (-2)
def history3 : List L := line3 :: history2
theorem sound3 : IsCPDerivation F history3 :=
  recode (IsCPDerivation.add (e := line0) (e' := line1) sound2 (earlier history2 2 (by decide)) (earlier history2 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line4 : L := dataLine [-2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0] (-3)
def history4 : List L := line4 :: history3
theorem sound4 : IsCPDerivation F history4 :=
  recode (IsCPDerivation.add (e := line3) (e' := line2) sound3 (earlier history3 0 (by decide)) (earlier history3 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line5 : L := dataLine [-1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history5 : List L := line5 :: history4
theorem sound5 : IsCPDerivation F history5 :=
  recode (IsCPDerivation.div (e := line4) 2 sound4 (earlier history4 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line6 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history6 : List L := line6 :: history5
theorem sound6 : IsCPDerivation F history6 :=
  recode (IsCPDerivation.ax (pair 0 0 3) sound5 (pairMem 0 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line7 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history7 : List L := line7 :: history6
theorem sound7 : IsCPDerivation F history7 :=
  recode (IsCPDerivation.ax (pair 0 1 3) sound6 (pairMem 0 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line8 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0] (-1)
def history8 : List L := line8 :: history7
theorem sound8 : IsCPDerivation F history8 :=
  recode (IsCPDerivation.ax (pair 0 2 3) sound7 (pairMem 0 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line9 : L := dataLine [-2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0] (-2)
def history9 : List L := line9 :: history8
theorem sound9 : IsCPDerivation F history9 :=
  recode (IsCPDerivation.mul (e := line5) 2 sound8 (earlier history8 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line10 : L := dataLine [-1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0] (-2)
def history10 : List L := line10 :: history9
theorem sound10 : IsCPDerivation F history10 :=
  recode (IsCPDerivation.add (e := line6) (e' := line7) sound9 (earlier history9 3 (by decide)) (earlier history9 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line11 : L := dataLine [-1, 0, 0, -1, 0, 0, -1, 0, 0, -3, 0, 0] (-3)
def history11 : List L := line11 :: history10
theorem sound11 : IsCPDerivation F history11 :=
  recode (IsCPDerivation.add (e := line10) (e' := line8) sound10 (earlier history10 0 (by decide)) (earlier history10 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line12 : L := dataLine [-3, 0, 0, -3, 0, 0, -3, 0, 0, -3, 0, 0] (-5)
def history12 : List L := line12 :: history11
theorem sound12 : IsCPDerivation F history12 :=
  recode (IsCPDerivation.add (e := line11) (e' := line9) sound11 (earlier history11 0 (by decide)) (earlier history11 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line13 : L := dataLine [-1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0] (-1)
def history13 : List L := line13 :: history12
theorem sound13 : IsCPDerivation F history13 :=
  recode (IsCPDerivation.div (e := line12) 3 sound12 (earlier history12 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line14 : L := dataLine [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history14 : List L := line14 :: history13
theorem sound14 : IsCPDerivation F history14 :=
  recode (IsCPDerivation.ax (pair 1 0 1) sound13 (pairMem 1 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line15 : L := dataLine [0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history15 : List L := line15 :: history14
theorem sound15 : IsCPDerivation F history15 :=
  recode (IsCPDerivation.ax (pair 1 0 2) sound14 (pairMem 1 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line16 : L := dataLine [0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0] (-1)
def history16 : List L := line16 :: history15
theorem sound16 : IsCPDerivation F history16 :=
  recode (IsCPDerivation.ax (pair 1 1 2) sound15 (pairMem 1 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line17 : L := dataLine [0, -2, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0] (-2)
def history17 : List L := line17 :: history16
theorem sound17 : IsCPDerivation F history17 :=
  recode (IsCPDerivation.add (e := line14) (e' := line15) sound16 (earlier history16 2 (by decide)) (earlier history16 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line18 : L := dataLine [0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0] (-3)
def history18 : List L := line18 :: history17
theorem sound18 : IsCPDerivation F history18 :=
  recode (IsCPDerivation.add (e := line17) (e' := line16) sound17 (earlier history17 0 (by decide)) (earlier history17 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line19 : L := dataLine [0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0] (-1)
def history19 : List L := line19 :: history18
theorem sound19 : IsCPDerivation F history19 :=
  recode (IsCPDerivation.div (e := line18) 2 sound18 (earlier history18 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line20 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history20 : List L := line20 :: history19
theorem sound20 : IsCPDerivation F history20 :=
  recode (IsCPDerivation.ax (pair 1 0 3) sound19 (pairMem 1 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line21 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0] (-1)
def history21 : List L := line21 :: history20
theorem sound21 : IsCPDerivation F history21 :=
  recode (IsCPDerivation.ax (pair 1 1 3) sound20 (pairMem 1 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line22 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0] (-1)
def history22 : List L := line22 :: history21
theorem sound22 : IsCPDerivation F history22 :=
  recode (IsCPDerivation.ax (pair 1 2 3) sound21 (pairMem 1 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line23 : L := dataLine [0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0] (-2)
def history23 : List L := line23 :: history22
theorem sound23 : IsCPDerivation F history23 :=
  recode (IsCPDerivation.mul (e := line19) 2 sound22 (earlier history22 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line24 : L := dataLine [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0] (-2)
def history24 : List L := line24 :: history23
theorem sound24 : IsCPDerivation F history24 :=
  recode (IsCPDerivation.add (e := line20) (e' := line21) sound23 (earlier history23 3 (by decide)) (earlier history23 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line25 : L := dataLine [0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -3, 0] (-3)
def history25 : List L := line25 :: history24
theorem sound25 : IsCPDerivation F history25 :=
  recode (IsCPDerivation.add (e := line24) (e' := line22) sound24 (earlier history24 0 (by decide)) (earlier history24 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line26 : L := dataLine [0, -3, 0, 0, -3, 0, 0, -3, 0, 0, -3, 0] (-5)
def history26 : List L := line26 :: history25
theorem sound26 : IsCPDerivation F history26 :=
  recode (IsCPDerivation.add (e := line25) (e' := line23) sound25 (earlier history25 0 (by decide)) (earlier history25 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line27 : L := dataLine [0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0] (-1)
def history27 : List L := line27 :: history26
theorem sound27 : IsCPDerivation F history27 :=
  recode (IsCPDerivation.div (e := line26) 3 sound26 (earlier history26 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line28 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history28 : List L := line28 :: history27
theorem sound28 : IsCPDerivation F history28 :=
  recode (IsCPDerivation.ax (pair 2 0 1) sound27 (pairMem 2 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line29 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history29 : List L := line29 :: history28
theorem sound29 : IsCPDerivation F history29 :=
  recode (IsCPDerivation.ax (pair 2 0 2) sound28 (pairMem 2 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line30 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-1)
def history30 : List L := line30 :: history29
theorem sound30 : IsCPDerivation F history30 :=
  recode (IsCPDerivation.ax (pair 2 1 2) sound29 (pairMem 2 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line31 : L := dataLine [0, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-2)
def history31 : List L := line31 :: history30
theorem sound31 : IsCPDerivation F history31 :=
  recode (IsCPDerivation.add (e := line28) (e' := line29) sound30 (earlier history30 2 (by decide)) (earlier history30 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line32 : L := dataLine [0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0] (-3)
def history32 : List L := line32 :: history31
theorem sound32 : IsCPDerivation F history32 :=
  recode (IsCPDerivation.add (e := line31) (e' := line30) sound31 (earlier history31 0 (by decide)) (earlier history31 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line33 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-1)
def history33 : List L := line33 :: history32
theorem sound33 : IsCPDerivation F history33 :=
  recode (IsCPDerivation.div (e := line32) 2 sound32 (earlier history32 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line34 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history34 : List L := line34 :: history33
theorem sound34 : IsCPDerivation F history34 :=
  recode (IsCPDerivation.ax (pair 2 0 3) sound33 (pairMem 2 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line35 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] (-1)
def history35 : List L := line35 :: history34
theorem sound35 : IsCPDerivation F history35 :=
  recode (IsCPDerivation.ax (pair 2 1 3) sound34 (pairMem 2 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line36 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1] (-1)
def history36 : List L := line36 :: history35
theorem sound36 : IsCPDerivation F history36 :=
  recode (IsCPDerivation.ax (pair 2 2 3) sound35 (pairMem 2 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line37 : L := dataLine [0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0] (-2)
def history37 : List L := line37 :: history36
theorem sound37 : IsCPDerivation F history37 :=
  recode (IsCPDerivation.mul (e := line33) 2 sound36 (earlier history36 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line38 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -2] (-2)
def history38 : List L := line38 :: history37
theorem sound38 : IsCPDerivation F history38 :=
  recode (IsCPDerivation.add (e := line34) (e' := line35) sound37 (earlier history37 3 (by decide)) (earlier history37 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line39 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -3] (-3)
def history39 : List L := line39 :: history38
theorem sound39 : IsCPDerivation F history39 :=
  recode (IsCPDerivation.add (e := line38) (e' := line36) sound38 (earlier history38 0 (by decide)) (earlier history38 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line40 : L := dataLine [0, 0, -3, 0, 0, -3, 0, 0, -3, 0, 0, -3] (-5)
def history40 : List L := line40 :: history39
theorem sound40 : IsCPDerivation F history40 :=
  recode (IsCPDerivation.add (e := line39) (e' := line37) sound39 (earlier history39 0 (by decide)) (earlier history39 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line41 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -1] (-1)
def history41 : List L := line41 :: history40
theorem sound41 : IsCPDerivation F history41 :=
  recode (IsCPDerivation.div (e := line40) 3 sound40 (earlier history40 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line42 : L := dataLine [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history42 : List L := line42 :: history41
theorem sound42 : IsCPDerivation F history42 :=
  recode (IsCPDerivation.ax (pigeon 0) sound41 (pigeonMem 0)) (by decide +kernel) (by decide +kernel)

def line43 : L := dataLine [0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0] (1)
def history43 : List L := line43 :: history42
theorem sound43 : IsCPDerivation F history43 :=
  recode (IsCPDerivation.ax (pigeon 1) sound42 (pigeonMem 1)) (by decide +kernel) (by decide +kernel)

def line44 : L := dataLine [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0] (1)
def history44 : List L := line44 :: history43
theorem sound44 : IsCPDerivation F history44 :=
  recode (IsCPDerivation.ax (pigeon 2) sound43 (pigeonMem 2)) (by decide +kernel) (by decide +kernel)

def line45 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] (1)
def history45 : List L := line45 :: history44
theorem sound45 : IsCPDerivation F history45 :=
  recode (IsCPDerivation.ax (pigeon 3) sound44 (pigeonMem 3)) (by decide +kernel) (by decide +kernel)

def line46 : L := dataLine [-1, -1, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0] (-2)
def history46 : List L := line46 :: history45
theorem sound46 : IsCPDerivation F history46 :=
  recode (IsCPDerivation.add (e := line13) (e' := line27) sound45 (earlier history45 32 (by decide)) (earlier history45 18 (by decide))) (by decide +kernel) (by decide +kernel)

def line47 : L := dataLine [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-3)
def history47 : List L := line47 :: history46
theorem sound47 : IsCPDerivation F history47 :=
  recode (IsCPDerivation.add (e := line46) (e' := line41) sound46 (earlier history46 0 (by decide)) (earlier history46 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line48 : L := dataLine [0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-2)
def history48 : List L := line48 :: history47
theorem sound48 : IsCPDerivation F history48 :=
  recode (IsCPDerivation.add (e := line47) (e' := line42) sound47 (earlier history47 0 (by decide)) (earlier history47 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line49 : L := dataLine [0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1] (-1)
def history49 : List L := line49 :: history48
theorem sound49 : IsCPDerivation F history49 :=
  recode (IsCPDerivation.add (e := line48) (e' := line43) sound48 (earlier history48 0 (by decide)) (earlier history48 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line50 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1] (0)
def history50 : List L := line50 :: history49
theorem sound50 : IsCPDerivation F history50 :=
  recode (IsCPDerivation.add (e := line49) (e' := line44) sound49 (earlier history49 0 (by decide)) (earlier history49 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line51 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history51 : List L := line51 :: history50
theorem sound51 : IsCPDerivation F history51 :=
  recode (IsCPDerivation.add (e := line50) (e' := line45) sound50 (earlier history50 0 (by decide)) (earlier history50 5 (by decide))) (by decide +kernel) (by decide +kernel)

theorem certificate : ∃ π : List L, IsCPRefutation F π ∧ π.length = 52 := by
  have eq : line51 = ((0 : V → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) rfl
  refine ⟨history51, ⟨sound51, ?_⟩, rfl⟩
  rw [← eq]
  exact earlier history51 0 (by decide)

end PEqualNP.Outside.L_meta_9682.Certificate
