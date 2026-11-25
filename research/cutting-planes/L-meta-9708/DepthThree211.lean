import PEqualNP.Defs

set_option maxRecDepth 4096

namespace PEqualNP.Outside.L_meta_9708.DepthThree
open PEqualNP.ProofComplexity PEqualNP.Search

abbrev V := Fin 6 × Fin 5
abbrev L := CPLine V
abbrev F := PHP 6 5

def pigeon (p : Fin 6) := Finset.univ.image (fun h : Fin 5 => ((p, h), true))
def pair (h : Fin 5) (p q : Fin 6) : Clause V := {((p, h), false), ((q, h), false)}

theorem pigeonMem (p : Fin 6) : pigeon p ∈ F := Or.inl ⟨p, rfl⟩
theorem pairMem (h : Fin 5) (p q : Fin 6) (ne : p ≠ q) : pair h p q ∈ F :=
  Or.inr ⟨p, q, h, ne, rfl⟩

def dataLine (coeffs : List ℤ) (rhs : ℤ) : L :=
  (fun v => coeffs.getD (5 * v.1.val + v.2.val) 0, rhs)

theorem recode {π : List L} {a b : L} (prev : IsCPDerivation F (a :: π))
    (hf : ∀ v, a.1 v = b.1 v) (hc : a.2 = b.2) : IsCPDerivation F (b :: π) := by
  have eq : a = b := Prod.ext (funext hf) hc
  rwa [← eq]

theorem earlier (xs : List L) (k : ℕ) (hk : k < xs.length) : xs[k] ∈ xs :=
  List.getElem_mem hk

def empty : List L := []
theorem start : IsCPDerivation F empty := .nil

def line0 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history0 : List L := line0 :: empty
theorem sound0 : IsCPDerivation F history0 :=
  recode (IsCPDerivation.ax (pair 0 0 1) start (pairMem 0 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line1 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history1 : List L := line1 :: history0
theorem sound1 : IsCPDerivation F history1 :=
  recode (IsCPDerivation.ax (pair 0 0 2) sound0 (pairMem 0 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line2 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history2 : List L := line2 :: history1
theorem sound2 : IsCPDerivation F history2 :=
  recode (IsCPDerivation.ax (pair 0 0 3) sound1 (pairMem 0 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line3 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history3 : List L := line3 :: history2
theorem sound3 : IsCPDerivation F history3 :=
  recode (IsCPDerivation.ax (pair 0 0 4) sound2 (pairMem 0 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line4 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history4 : List L := line4 :: history3
theorem sound4 : IsCPDerivation F history4 :=
  recode (IsCPDerivation.ax (pair 0 0 5) sound3 (pairMem 0 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line5 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history5 : List L := line5 :: history4
theorem sound5 : IsCPDerivation F history5 :=
  recode (IsCPDerivation.ax (pair 0 1 2) sound4 (pairMem 0 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line6 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history6 : List L := line6 :: history5
theorem sound6 : IsCPDerivation F history6 :=
  recode (IsCPDerivation.ax (pair 0 1 3) sound5 (pairMem 0 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line7 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history7 : List L := line7 :: history6
theorem sound7 : IsCPDerivation F history7 :=
  recode (IsCPDerivation.ax (pair 0 1 4) sound6 (pairMem 0 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line8 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history8 : List L := line8 :: history7
theorem sound8 : IsCPDerivation F history8 :=
  recode (IsCPDerivation.ax (pair 0 1 5) sound7 (pairMem 0 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line9 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history9 : List L := line9 :: history8
theorem sound9 : IsCPDerivation F history9 :=
  recode (IsCPDerivation.ax (pair 0 2 3) sound8 (pairMem 0 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line10 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history10 : List L := line10 :: history9
theorem sound10 : IsCPDerivation F history10 :=
  recode (IsCPDerivation.ax (pair 0 2 4) sound9 (pairMem 0 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line11 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history11 : List L := line11 :: history10
theorem sound11 : IsCPDerivation F history11 :=
  recode (IsCPDerivation.ax (pair 0 2 5) sound10 (pairMem 0 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line12 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history12 : List L := line12 :: history11
theorem sound12 : IsCPDerivation F history12 :=
  recode (IsCPDerivation.ax (pair 0 3 4) sound11 (pairMem 0 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line13 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history13 : List L := line13 :: history12
theorem sound13 : IsCPDerivation F history13 :=
  recode (IsCPDerivation.ax (pair 0 3 5) sound12 (pairMem 0 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line14 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history14 : List L := line14 :: history13
theorem sound14 : IsCPDerivation F history14 :=
  recode (IsCPDerivation.ax (pair 0 4 5) sound13 (pairMem 0 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line15 : L := dataLine [-2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history15 : List L := line15 :: history14
theorem sound15 : IsCPDerivation F history15 :=
  recode (IsCPDerivation.add (e := line0) (e' := line1) sound14 (earlier history14 14 (by decide)) (earlier history14 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line16 : L := dataLine [-2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history16 : List L := line16 :: history15
theorem sound16 : IsCPDerivation F history16 :=
  recode (IsCPDerivation.add (e := line15) (e' := line5) sound15 (earlier history15 0 (by decide)) (earlier history15 10 (by decide))) (by decide +kernel) (by decide +kernel)

def line17 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history17 : List L := line17 :: history16
theorem sound17 : IsCPDerivation F history17 :=
  recode (IsCPDerivation.div (e := line16) 2 sound16 (earlier history16 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line18 : L := dataLine [-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history18 : List L := line18 :: history17
theorem sound18 : IsCPDerivation F history18 :=
  recode (IsCPDerivation.add (e := line2) (e' := line3) sound17 (earlier history17 15 (by decide)) (earlier history17 14 (by decide))) (by decide +kernel) (by decide +kernel)

def line19 : L := dataLine [-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history19 : List L := line19 :: history18
theorem sound19 : IsCPDerivation F history19 :=
  recode (IsCPDerivation.add (e := line18) (e' := line12) sound18 (earlier history18 0 (by decide)) (earlier history18 6 (by decide))) (by decide +kernel) (by decide +kernel)

def line20 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history20 : List L := line20 :: history19
theorem sound20 : IsCPDerivation F history20 :=
  recode (IsCPDerivation.div (e := line19) 2 sound19 (earlier history19 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line21 : L := dataLine [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history21 : List L := line21 :: history20
theorem sound21 : IsCPDerivation F history21 :=
  recode (IsCPDerivation.add (e := line6) (e' := line7) sound20 (earlier history20 14 (by decide)) (earlier history20 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line22 : L := dataLine [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history22 : List L := line22 :: history21
theorem sound22 : IsCPDerivation F history22 :=
  recode (IsCPDerivation.add (e := line21) (e' := line12) sound21 (earlier history21 0 (by decide)) (earlier history21 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line23 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history23 : List L := line23 :: history22
theorem sound23 : IsCPDerivation F history23 :=
  recode (IsCPDerivation.div (e := line22) 2 sound22 (earlier history22 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line24 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history24 : List L := line24 :: history23
theorem sound24 : IsCPDerivation F history24 :=
  recode (IsCPDerivation.add (e := line9) (e' := line10) sound23 (earlier history23 14 (by decide)) (earlier history23 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line25 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history25 : List L := line25 :: history24
theorem sound25 : IsCPDerivation F history25 :=
  recode (IsCPDerivation.add (e := line24) (e' := line12) sound24 (earlier history24 0 (by decide)) (earlier history24 12 (by decide))) (by decide +kernel) (by decide +kernel)

def line26 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history26 : List L := line26 :: history25
theorem sound26 : IsCPDerivation F history26 :=
  recode (IsCPDerivation.div (e := line25) 2 sound25 (earlier history25 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line27 : L := dataLine [-2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history27 : List L := line27 :: history26
theorem sound27 : IsCPDerivation F history27 :=
  recode (IsCPDerivation.mul (e := line17) 2 sound26 (earlier history26 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line28 : L := dataLine [-3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history28 : List L := line28 :: history27
theorem sound28 : IsCPDerivation F history28 :=
  recode (IsCPDerivation.add (e := line27) (e' := line20) sound27 (earlier history27 0 (by decide)) (earlier history27 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line29 : L := dataLine [-3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history29 : List L := line29 :: history28
theorem sound29 : IsCPDerivation F history29 :=
  recode (IsCPDerivation.add (e := line28) (e' := line23) sound28 (earlier history28 0 (by decide)) (earlier history28 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line30 : L := dataLine [-3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history30 : List L := line30 :: history29
theorem sound30 : IsCPDerivation F history30 :=
  recode (IsCPDerivation.add (e := line29) (e' := line26) sound29 (earlier history29 0 (by decide)) (earlier history29 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line31 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history31 : List L := line31 :: history30
theorem sound31 : IsCPDerivation F history31 :=
  recode (IsCPDerivation.div (e := line30) 3 sound30 (earlier history30 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line32 : L := dataLine [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history32 : List L := line32 :: history31
theorem sound32 : IsCPDerivation F history32 :=
  recode (IsCPDerivation.mul (e := line31) 4 sound31 (earlier history31 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line33 : L := dataLine [-5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-5)
def history33 : List L := line33 :: history32
theorem sound33 : IsCPDerivation F history33 :=
  recode (IsCPDerivation.add (e := line32) (e' := line4) sound32 (earlier history32 0 (by decide)) (earlier history32 28 (by decide))) (by decide +kernel) (by decide +kernel)

def line34 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0, 0] (-6)
def history34 : List L := line34 :: history33
theorem sound34 : IsCPDerivation F history34 :=
  recode (IsCPDerivation.add (e := line33) (e' := line8) sound33 (earlier history33 0 (by decide)) (earlier history33 25 (by decide))) (by decide +kernel) (by decide +kernel)

def line35 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0] (-7)
def history35 : List L := line35 :: history34
theorem sound35 : IsCPDerivation F history35 :=
  recode (IsCPDerivation.add (e := line34) (e' := line11) sound34 (earlier history34 0 (by decide)) (earlier history34 23 (by decide))) (by decide +kernel) (by decide +kernel)

def line36 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0] (-8)
def history36 : List L := line36 :: history35
theorem sound36 : IsCPDerivation F history36 :=
  recode (IsCPDerivation.add (e := line35) (e' := line13) sound35 (earlier history35 0 (by decide)) (earlier history35 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line37 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0] (-9)
def history37 : List L := line37 :: history36
theorem sound37 : IsCPDerivation F history37 :=
  recode (IsCPDerivation.add (e := line36) (e' := line14) sound36 (earlier history36 0 (by decide)) (earlier history36 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line38 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history38 : List L := line38 :: history37
theorem sound38 : IsCPDerivation F history38 :=
  recode (IsCPDerivation.div (e := line37) 5 sound37 (earlier history37 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line39 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history39 : List L := line39 :: history38
theorem sound39 : IsCPDerivation F history39 :=
  recode (IsCPDerivation.ax (pair 1 0 1) sound38 (pairMem 1 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line40 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history40 : List L := line40 :: history39
theorem sound40 : IsCPDerivation F history40 :=
  recode (IsCPDerivation.ax (pair 1 0 2) sound39 (pairMem 1 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line41 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history41 : List L := line41 :: history40
theorem sound41 : IsCPDerivation F history41 :=
  recode (IsCPDerivation.ax (pair 1 0 3) sound40 (pairMem 1 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line42 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history42 : List L := line42 :: history41
theorem sound42 : IsCPDerivation F history42 :=
  recode (IsCPDerivation.ax (pair 1 0 4) sound41 (pairMem 1 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line43 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history43 : List L := line43 :: history42
theorem sound43 : IsCPDerivation F history43 :=
  recode (IsCPDerivation.ax (pair 1 0 5) sound42 (pairMem 1 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line44 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history44 : List L := line44 :: history43
theorem sound44 : IsCPDerivation F history44 :=
  recode (IsCPDerivation.ax (pair 1 1 2) sound43 (pairMem 1 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line45 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history45 : List L := line45 :: history44
theorem sound45 : IsCPDerivation F history45 :=
  recode (IsCPDerivation.ax (pair 1 1 3) sound44 (pairMem 1 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line46 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history46 : List L := line46 :: history45
theorem sound46 : IsCPDerivation F history46 :=
  recode (IsCPDerivation.ax (pair 1 1 4) sound45 (pairMem 1 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line47 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history47 : List L := line47 :: history46
theorem sound47 : IsCPDerivation F history47 :=
  recode (IsCPDerivation.ax (pair 1 1 5) sound46 (pairMem 1 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line48 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history48 : List L := line48 :: history47
theorem sound48 : IsCPDerivation F history48 :=
  recode (IsCPDerivation.ax (pair 1 2 3) sound47 (pairMem 1 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line49 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history49 : List L := line49 :: history48
theorem sound49 : IsCPDerivation F history49 :=
  recode (IsCPDerivation.ax (pair 1 2 4) sound48 (pairMem 1 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line50 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history50 : List L := line50 :: history49
theorem sound50 : IsCPDerivation F history50 :=
  recode (IsCPDerivation.ax (pair 1 2 5) sound49 (pairMem 1 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line51 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history51 : List L := line51 :: history50
theorem sound51 : IsCPDerivation F history51 :=
  recode (IsCPDerivation.ax (pair 1 3 4) sound50 (pairMem 1 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line52 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history52 : List L := line52 :: history51
theorem sound52 : IsCPDerivation F history52 :=
  recode (IsCPDerivation.ax (pair 1 3 5) sound51 (pairMem 1 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line53 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history53 : List L := line53 :: history52
theorem sound53 : IsCPDerivation F history53 :=
  recode (IsCPDerivation.ax (pair 1 4 5) sound52 (pairMem 1 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line54 : L := dataLine [0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history54 : List L := line54 :: history53
theorem sound54 : IsCPDerivation F history54 :=
  recode (IsCPDerivation.add (e := line39) (e' := line40) sound53 (earlier history53 14 (by decide)) (earlier history53 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line55 : L := dataLine [0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history55 : List L := line55 :: history54
theorem sound55 : IsCPDerivation F history55 :=
  recode (IsCPDerivation.add (e := line54) (e' := line44) sound54 (earlier history54 0 (by decide)) (earlier history54 10 (by decide))) (by decide +kernel) (by decide +kernel)

def line56 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history56 : List L := line56 :: history55
theorem sound56 : IsCPDerivation F history56 :=
  recode (IsCPDerivation.div (e := line55) 2 sound55 (earlier history55 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line57 : L := dataLine [0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history57 : List L := line57 :: history56
theorem sound57 : IsCPDerivation F history57 :=
  recode (IsCPDerivation.add (e := line41) (e' := line42) sound56 (earlier history56 15 (by decide)) (earlier history56 14 (by decide))) (by decide +kernel) (by decide +kernel)

def line58 : L := dataLine [0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history58 : List L := line58 :: history57
theorem sound58 : IsCPDerivation F history58 :=
  recode (IsCPDerivation.add (e := line57) (e' := line51) sound57 (earlier history57 0 (by decide)) (earlier history57 6 (by decide))) (by decide +kernel) (by decide +kernel)

def line59 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history59 : List L := line59 :: history58
theorem sound59 : IsCPDerivation F history59 :=
  recode (IsCPDerivation.div (e := line58) 2 sound58 (earlier history58 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line60 : L := dataLine [0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history60 : List L := line60 :: history59
theorem sound60 : IsCPDerivation F history60 :=
  recode (IsCPDerivation.add (e := line45) (e' := line46) sound59 (earlier history59 14 (by decide)) (earlier history59 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line61 : L := dataLine [0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history61 : List L := line61 :: history60
theorem sound61 : IsCPDerivation F history61 :=
  recode (IsCPDerivation.add (e := line60) (e' := line51) sound60 (earlier history60 0 (by decide)) (earlier history60 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line62 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history62 : List L := line62 :: history61
theorem sound62 : IsCPDerivation F history62 :=
  recode (IsCPDerivation.div (e := line61) 2 sound61 (earlier history61 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line63 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history63 : List L := line63 :: history62
theorem sound63 : IsCPDerivation F history63 :=
  recode (IsCPDerivation.add (e := line48) (e' := line49) sound62 (earlier history62 14 (by decide)) (earlier history62 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line64 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history64 : List L := line64 :: history63
theorem sound64 : IsCPDerivation F history64 :=
  recode (IsCPDerivation.add (e := line63) (e' := line51) sound63 (earlier history63 0 (by decide)) (earlier history63 12 (by decide))) (by decide +kernel) (by decide +kernel)

def line65 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history65 : List L := line65 :: history64
theorem sound65 : IsCPDerivation F history65 :=
  recode (IsCPDerivation.div (e := line64) 2 sound64 (earlier history64 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line66 : L := dataLine [0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history66 : List L := line66 :: history65
theorem sound66 : IsCPDerivation F history66 :=
  recode (IsCPDerivation.mul (e := line56) 2 sound65 (earlier history65 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line67 : L := dataLine [0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history67 : List L := line67 :: history66
theorem sound67 : IsCPDerivation F history67 :=
  recode (IsCPDerivation.add (e := line66) (e' := line59) sound66 (earlier history66 0 (by decide)) (earlier history66 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line68 : L := dataLine [0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history68 : List L := line68 :: history67
theorem sound68 : IsCPDerivation F history68 :=
  recode (IsCPDerivation.add (e := line67) (e' := line62) sound67 (earlier history67 0 (by decide)) (earlier history67 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line69 : L := dataLine [0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history69 : List L := line69 :: history68
theorem sound69 : IsCPDerivation F history69 :=
  recode (IsCPDerivation.add (e := line68) (e' := line65) sound68 (earlier history68 0 (by decide)) (earlier history68 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line70 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history70 : List L := line70 :: history69
theorem sound70 : IsCPDerivation F history70 :=
  recode (IsCPDerivation.div (e := line69) 3 sound69 (earlier history69 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line71 : L := dataLine [0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history71 : List L := line71 :: history70
theorem sound71 : IsCPDerivation F history71 :=
  recode (IsCPDerivation.mul (e := line70) 4 sound70 (earlier history70 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line72 : L := dataLine [0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0] (-5)
def history72 : List L := line72 :: history71
theorem sound72 : IsCPDerivation F history72 :=
  recode (IsCPDerivation.add (e := line71) (e' := line43) sound71 (earlier history71 0 (by decide)) (earlier history71 28 (by decide))) (by decide +kernel) (by decide +kernel)

def line73 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0] (-6)
def history73 : List L := line73 :: history72
theorem sound73 : IsCPDerivation F history73 :=
  recode (IsCPDerivation.add (e := line72) (e' := line47) sound72 (earlier history72 0 (by decide)) (earlier history72 25 (by decide))) (by decide +kernel) (by decide +kernel)

def line74 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0] (-7)
def history74 : List L := line74 :: history73
theorem sound74 : IsCPDerivation F history74 :=
  recode (IsCPDerivation.add (e := line73) (e' := line50) sound73 (earlier history73 0 (by decide)) (earlier history73 23 (by decide))) (by decide +kernel) (by decide +kernel)

def line75 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0] (-8)
def history75 : List L := line75 :: history74
theorem sound75 : IsCPDerivation F history75 :=
  recode (IsCPDerivation.add (e := line74) (e' := line52) sound74 (earlier history74 0 (by decide)) (earlier history74 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line76 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0] (-9)
def history76 : List L := line76 :: history75
theorem sound76 : IsCPDerivation F history76 :=
  recode (IsCPDerivation.add (e := line75) (e' := line53) sound75 (earlier history75 0 (by decide)) (earlier history75 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line77 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history77 : List L := line77 :: history76
theorem sound77 : IsCPDerivation F history77 :=
  recode (IsCPDerivation.div (e := line76) 5 sound76 (earlier history76 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line78 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history78 : List L := line78 :: history77
theorem sound78 : IsCPDerivation F history78 :=
  recode (IsCPDerivation.ax (pair 2 0 1) sound77 (pairMem 2 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line79 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history79 : List L := line79 :: history78
theorem sound79 : IsCPDerivation F history79 :=
  recode (IsCPDerivation.ax (pair 2 0 2) sound78 (pairMem 2 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line80 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history80 : List L := line80 :: history79
theorem sound80 : IsCPDerivation F history80 :=
  recode (IsCPDerivation.ax (pair 2 0 3) sound79 (pairMem 2 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line81 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history81 : List L := line81 :: history80
theorem sound81 : IsCPDerivation F history81 :=
  recode (IsCPDerivation.ax (pair 2 0 4) sound80 (pairMem 2 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line82 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history82 : List L := line82 :: history81
theorem sound82 : IsCPDerivation F history82 :=
  recode (IsCPDerivation.ax (pair 2 0 5) sound81 (pairMem 2 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line83 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history83 : List L := line83 :: history82
theorem sound83 : IsCPDerivation F history83 :=
  recode (IsCPDerivation.ax (pair 2 1 2) sound82 (pairMem 2 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line84 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history84 : List L := line84 :: history83
theorem sound84 : IsCPDerivation F history84 :=
  recode (IsCPDerivation.ax (pair 2 1 3) sound83 (pairMem 2 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line85 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history85 : List L := line85 :: history84
theorem sound85 : IsCPDerivation F history85 :=
  recode (IsCPDerivation.ax (pair 2 1 4) sound84 (pairMem 2 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line86 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history86 : List L := line86 :: history85
theorem sound86 : IsCPDerivation F history86 :=
  recode (IsCPDerivation.ax (pair 2 1 5) sound85 (pairMem 2 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line87 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history87 : List L := line87 :: history86
theorem sound87 : IsCPDerivation F history87 :=
  recode (IsCPDerivation.ax (pair 2 2 3) sound86 (pairMem 2 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line88 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history88 : List L := line88 :: history87
theorem sound88 : IsCPDerivation F history88 :=
  recode (IsCPDerivation.ax (pair 2 2 4) sound87 (pairMem 2 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line89 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history89 : List L := line89 :: history88
theorem sound89 : IsCPDerivation F history89 :=
  recode (IsCPDerivation.ax (pair 2 2 5) sound88 (pairMem 2 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line90 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history90 : List L := line90 :: history89
theorem sound90 : IsCPDerivation F history90 :=
  recode (IsCPDerivation.ax (pair 2 3 4) sound89 (pairMem 2 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line91 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history91 : List L := line91 :: history90
theorem sound91 : IsCPDerivation F history91 :=
  recode (IsCPDerivation.ax (pair 2 3 5) sound90 (pairMem 2 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line92 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0] (-1)
def history92 : List L := line92 :: history91
theorem sound92 : IsCPDerivation F history92 :=
  recode (IsCPDerivation.ax (pair 2 4 5) sound91 (pairMem 2 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line93 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history93 : List L := line93 :: history92
theorem sound93 : IsCPDerivation F history93 :=
  recode (IsCPDerivation.add (e := line78) (e' := line79) sound92 (earlier history92 14 (by decide)) (earlier history92 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line94 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history94 : List L := line94 :: history93
theorem sound94 : IsCPDerivation F history94 :=
  recode (IsCPDerivation.add (e := line93) (e' := line83) sound93 (earlier history93 0 (by decide)) (earlier history93 10 (by decide))) (by decide +kernel) (by decide +kernel)

def line95 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history95 : List L := line95 :: history94
theorem sound95 : IsCPDerivation F history95 :=
  recode (IsCPDerivation.div (e := line94) 2 sound94 (earlier history94 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line96 : L := dataLine [0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-2)
def history96 : List L := line96 :: history95
theorem sound96 : IsCPDerivation F history96 :=
  recode (IsCPDerivation.add (e := line80) (e' := line81) sound95 (earlier history95 15 (by decide)) (earlier history95 14 (by decide))) (by decide +kernel) (by decide +kernel)

def line97 : L := dataLine [0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] (-3)
def history97 : List L := line97 :: history96
theorem sound97 : IsCPDerivation F history97 :=
  recode (IsCPDerivation.add (e := line96) (e' := line90) sound96 (earlier history96 0 (by decide)) (earlier history96 6 (by decide))) (by decide +kernel) (by decide +kernel)

def line98 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history98 : List L := line98 :: history97
theorem sound98 : IsCPDerivation F history98 :=
  recode (IsCPDerivation.div (e := line97) 2 sound97 (earlier history97 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line99 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-2)
def history99 : List L := line99 :: history98
theorem sound99 : IsCPDerivation F history99 :=
  recode (IsCPDerivation.add (e := line84) (e' := line85) sound98 (earlier history98 14 (by decide)) (earlier history98 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line100 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] (-3)
def history100 : List L := line100 :: history99
theorem sound100 : IsCPDerivation F history100 :=
  recode (IsCPDerivation.add (e := line99) (e' := line90) sound99 (earlier history99 0 (by decide)) (earlier history99 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line101 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history101 : List L := line101 :: history100
theorem sound101 : IsCPDerivation F history101 :=
  recode (IsCPDerivation.div (e := line100) 2 sound100 (earlier history100 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line102 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-2)
def history102 : List L := line102 :: history101
theorem sound102 : IsCPDerivation F history102 :=
  recode (IsCPDerivation.add (e := line87) (e' := line88) sound101 (earlier history101 14 (by decide)) (earlier history101 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line103 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] (-3)
def history103 : List L := line103 :: history102
theorem sound103 : IsCPDerivation F history103 :=
  recode (IsCPDerivation.add (e := line102) (e' := line90) sound102 (earlier history102 0 (by decide)) (earlier history102 12 (by decide))) (by decide +kernel) (by decide +kernel)

def line104 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history104 : List L := line104 :: history103
theorem sound104 : IsCPDerivation F history104 :=
  recode (IsCPDerivation.div (e := line103) 2 sound103 (earlier history103 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line105 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history105 : List L := line105 :: history104
theorem sound105 : IsCPDerivation F history105 :=
  recode (IsCPDerivation.mul (e := line95) 2 sound104 (earlier history104 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line106 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-3)
def history106 : List L := line106 :: history105
theorem sound106 : IsCPDerivation F history106 :=
  recode (IsCPDerivation.add (e := line105) (e' := line98) sound105 (earlier history105 0 (by decide)) (earlier history105 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line107 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] (-4)
def history107 : List L := line107 :: history106
theorem sound107 : IsCPDerivation F history107 :=
  recode (IsCPDerivation.add (e := line106) (e' := line101) sound106 (earlier history106 0 (by decide)) (earlier history106 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line108 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0] (-5)
def history108 : List L := line108 :: history107
theorem sound108 : IsCPDerivation F history108 :=
  recode (IsCPDerivation.add (e := line107) (e' := line104) sound107 (earlier history107 0 (by decide)) (earlier history107 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line109 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history109 : List L := line109 :: history108
theorem sound109 : IsCPDerivation F history109 :=
  recode (IsCPDerivation.div (e := line108) 3 sound108 (earlier history108 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line110 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0] (-4)
def history110 : List L := line110 :: history109
theorem sound110 : IsCPDerivation F history110 :=
  recode (IsCPDerivation.mul (e := line109) 4 sound109 (earlier history109 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line111 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0] (-5)
def history111 : List L := line111 :: history110
theorem sound111 : IsCPDerivation F history111 :=
  recode (IsCPDerivation.add (e := line110) (e' := line82) sound110 (earlier history110 0 (by decide)) (earlier history110 28 (by decide))) (by decide +kernel) (by decide +kernel)

def line112 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0] (-6)
def history112 : List L := line112 :: history111
theorem sound112 : IsCPDerivation F history112 :=
  recode (IsCPDerivation.add (e := line111) (e' := line86) sound111 (earlier history111 0 (by decide)) (earlier history111 25 (by decide))) (by decide +kernel) (by decide +kernel)

def line113 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0] (-7)
def history113 : List L := line113 :: history112
theorem sound113 : IsCPDerivation F history113 :=
  recode (IsCPDerivation.add (e := line112) (e' := line89) sound112 (earlier history112 0 (by decide)) (earlier history112 23 (by decide))) (by decide +kernel) (by decide +kernel)

def line114 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0] (-8)
def history114 : List L := line114 :: history113
theorem sound114 : IsCPDerivation F history114 :=
  recode (IsCPDerivation.add (e := line113) (e' := line91) sound113 (earlier history113 0 (by decide)) (earlier history113 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line115 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0] (-9)
def history115 : List L := line115 :: history114
theorem sound115 : IsCPDerivation F history115 :=
  recode (IsCPDerivation.add (e := line114) (e' := line92) sound114 (earlier history114 0 (by decide)) (earlier history114 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line116 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0] (-1)
def history116 : List L := line116 :: history115
theorem sound116 : IsCPDerivation F history116 :=
  recode (IsCPDerivation.div (e := line115) 5 sound115 (earlier history115 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line117 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history117 : List L := line117 :: history116
theorem sound117 : IsCPDerivation F history117 :=
  recode (IsCPDerivation.ax (pair 3 0 1) sound116 (pairMem 3 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line118 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history118 : List L := line118 :: history117
theorem sound118 : IsCPDerivation F history118 :=
  recode (IsCPDerivation.ax (pair 3 0 2) sound117 (pairMem 3 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line119 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history119 : List L := line119 :: history118
theorem sound119 : IsCPDerivation F history119 :=
  recode (IsCPDerivation.ax (pair 3 0 3) sound118 (pairMem 3 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line120 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history120 : List L := line120 :: history119
theorem sound120 : IsCPDerivation F history120 :=
  recode (IsCPDerivation.ax (pair 3 0 4) sound119 (pairMem 3 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line121 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history121 : List L := line121 :: history120
theorem sound121 : IsCPDerivation F history121 :=
  recode (IsCPDerivation.ax (pair 3 0 5) sound120 (pairMem 3 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line122 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history122 : List L := line122 :: history121
theorem sound122 : IsCPDerivation F history122 :=
  recode (IsCPDerivation.ax (pair 3 1 2) sound121 (pairMem 3 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line123 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history123 : List L := line123 :: history122
theorem sound123 : IsCPDerivation F history123 :=
  recode (IsCPDerivation.ax (pair 3 1 3) sound122 (pairMem 3 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line124 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history124 : List L := line124 :: history123
theorem sound124 : IsCPDerivation F history124 :=
  recode (IsCPDerivation.ax (pair 3 1 4) sound123 (pairMem 3 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line125 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history125 : List L := line125 :: history124
theorem sound125 : IsCPDerivation F history125 :=
  recode (IsCPDerivation.ax (pair 3 1 5) sound124 (pairMem 3 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line126 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history126 : List L := line126 :: history125
theorem sound126 : IsCPDerivation F history126 :=
  recode (IsCPDerivation.ax (pair 3 2 3) sound125 (pairMem 3 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line127 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history127 : List L := line127 :: history126
theorem sound127 : IsCPDerivation F history127 :=
  recode (IsCPDerivation.ax (pair 3 2 4) sound126 (pairMem 3 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line128 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history128 : List L := line128 :: history127
theorem sound128 : IsCPDerivation F history128 :=
  recode (IsCPDerivation.ax (pair 3 2 5) sound127 (pairMem 3 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line129 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history129 : List L := line129 :: history128
theorem sound129 : IsCPDerivation F history129 :=
  recode (IsCPDerivation.ax (pair 3 3 4) sound128 (pairMem 3 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line130 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history130 : List L := line130 :: history129
theorem sound130 : IsCPDerivation F history130 :=
  recode (IsCPDerivation.ax (pair 3 3 5) sound129 (pairMem 3 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line131 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] (-1)
def history131 : List L := line131 :: history130
theorem sound131 : IsCPDerivation F history131 :=
  recode (IsCPDerivation.ax (pair 3 4 5) sound130 (pairMem 3 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line132 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history132 : List L := line132 :: history131
theorem sound132 : IsCPDerivation F history132 :=
  recode (IsCPDerivation.add (e := line117) (e' := line118) sound131 (earlier history131 14 (by decide)) (earlier history131 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line133 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history133 : List L := line133 :: history132
theorem sound133 : IsCPDerivation F history133 :=
  recode (IsCPDerivation.add (e := line132) (e' := line122) sound132 (earlier history132 0 (by decide)) (earlier history132 10 (by decide))) (by decide +kernel) (by decide +kernel)

def line134 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history134 : List L := line134 :: history133
theorem sound134 : IsCPDerivation F history134 :=
  recode (IsCPDerivation.div (e := line133) 2 sound133 (earlier history133 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line135 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-2)
def history135 : List L := line135 :: history134
theorem sound135 : IsCPDerivation F history135 :=
  recode (IsCPDerivation.add (e := line119) (e' := line120) sound134 (earlier history134 15 (by decide)) (earlier history134 14 (by decide))) (by decide +kernel) (by decide +kernel)

def line136 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] (-3)
def history136 : List L := line136 :: history135
theorem sound136 : IsCPDerivation F history136 :=
  recode (IsCPDerivation.add (e := line135) (e' := line129) sound135 (earlier history135 0 (by decide)) (earlier history135 6 (by decide))) (by decide +kernel) (by decide +kernel)

def line137 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history137 : List L := line137 :: history136
theorem sound137 : IsCPDerivation F history137 :=
  recode (IsCPDerivation.div (e := line136) 2 sound136 (earlier history136 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line138 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-2)
def history138 : List L := line138 :: history137
theorem sound138 : IsCPDerivation F history138 :=
  recode (IsCPDerivation.add (e := line123) (e' := line124) sound137 (earlier history137 14 (by decide)) (earlier history137 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line139 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] (-3)
def history139 : List L := line139 :: history138
theorem sound139 : IsCPDerivation F history139 :=
  recode (IsCPDerivation.add (e := line138) (e' := line129) sound138 (earlier history138 0 (by decide)) (earlier history138 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line140 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history140 : List L := line140 :: history139
theorem sound140 : IsCPDerivation F history140 :=
  recode (IsCPDerivation.div (e := line139) 2 sound139 (earlier history139 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line141 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-2)
def history141 : List L := line141 :: history140
theorem sound141 : IsCPDerivation F history141 :=
  recode (IsCPDerivation.add (e := line126) (e' := line127) sound140 (earlier history140 14 (by decide)) (earlier history140 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line142 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] (-3)
def history142 : List L := line142 :: history141
theorem sound142 : IsCPDerivation F history142 :=
  recode (IsCPDerivation.add (e := line141) (e' := line129) sound141 (earlier history141 0 (by decide)) (earlier history141 12 (by decide))) (by decide +kernel) (by decide +kernel)

def line143 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history143 : List L := line143 :: history142
theorem sound143 : IsCPDerivation F history143 :=
  recode (IsCPDerivation.div (e := line142) 2 sound142 (earlier history142 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line144 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history144 : List L := line144 :: history143
theorem sound144 : IsCPDerivation F history144 :=
  recode (IsCPDerivation.mul (e := line134) 2 sound143 (earlier history143 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line145 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-3)
def history145 : List L := line145 :: history144
theorem sound145 : IsCPDerivation F history145 :=
  recode (IsCPDerivation.add (e := line144) (e' := line137) sound144 (earlier history144 0 (by decide)) (earlier history144 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line146 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] (-4)
def history146 : List L := line146 :: history145
theorem sound146 : IsCPDerivation F history146 :=
  recode (IsCPDerivation.add (e := line145) (e' := line140) sound145 (earlier history145 0 (by decide)) (earlier history145 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line147 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0] (-5)
def history147 : List L := line147 :: history146
theorem sound147 : IsCPDerivation F history147 :=
  recode (IsCPDerivation.add (e := line146) (e' := line143) sound146 (earlier history146 0 (by decide)) (earlier history146 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line148 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history148 : List L := line148 :: history147
theorem sound148 : IsCPDerivation F history148 :=
  recode (IsCPDerivation.div (e := line147) 3 sound147 (earlier history147 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line149 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] (-4)
def history149 : List L := line149 :: history148
theorem sound149 : IsCPDerivation F history149 :=
  recode (IsCPDerivation.mul (e := line148) 4 sound148 (earlier history148 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line150 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0] (-5)
def history150 : List L := line150 :: history149
theorem sound150 : IsCPDerivation F history150 :=
  recode (IsCPDerivation.add (e := line149) (e' := line121) sound149 (earlier history149 0 (by decide)) (earlier history149 28 (by decide))) (by decide +kernel) (by decide +kernel)

def line151 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0] (-6)
def history151 : List L := line151 :: history150
theorem sound151 : IsCPDerivation F history151 :=
  recode (IsCPDerivation.add (e := line150) (e' := line125) sound150 (earlier history150 0 (by decide)) (earlier history150 25 (by decide))) (by decide +kernel) (by decide +kernel)

def line152 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0] (-7)
def history152 : List L := line152 :: history151
theorem sound152 : IsCPDerivation F history152 :=
  recode (IsCPDerivation.add (e := line151) (e' := line128) sound151 (earlier history151 0 (by decide)) (earlier history151 23 (by decide))) (by decide +kernel) (by decide +kernel)

def line153 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0] (-8)
def history153 : List L := line153 :: history152
theorem sound153 : IsCPDerivation F history153 :=
  recode (IsCPDerivation.add (e := line152) (e' := line130) sound152 (earlier history152 0 (by decide)) (earlier history152 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line154 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0] (-9)
def history154 : List L := line154 :: history153
theorem sound154 : IsCPDerivation F history154 :=
  recode (IsCPDerivation.add (e := line153) (e' := line131) sound153 (earlier history153 0 (by decide)) (earlier history153 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line155 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] (-1)
def history155 : List L := line155 :: history154
theorem sound155 : IsCPDerivation F history155 :=
  recode (IsCPDerivation.div (e := line154) 5 sound154 (earlier history154 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line156 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history156 : List L := line156 :: history155
theorem sound156 : IsCPDerivation F history156 :=
  recode (IsCPDerivation.ax (pair 4 0 1) sound155 (pairMem 4 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line157 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history157 : List L := line157 :: history156
theorem sound157 : IsCPDerivation F history157 :=
  recode (IsCPDerivation.ax (pair 4 0 2) sound156 (pairMem 4 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line158 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history158 : List L := line158 :: history157
theorem sound158 : IsCPDerivation F history158 :=
  recode (IsCPDerivation.ax (pair 4 0 3) sound157 (pairMem 4 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line159 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history159 : List L := line159 :: history158
theorem sound159 : IsCPDerivation F history159 :=
  recode (IsCPDerivation.ax (pair 4 0 4) sound158 (pairMem 4 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line160 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history160 : List L := line160 :: history159
theorem sound160 : IsCPDerivation F history160 :=
  recode (IsCPDerivation.ax (pair 4 0 5) sound159 (pairMem 4 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line161 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history161 : List L := line161 :: history160
theorem sound161 : IsCPDerivation F history161 :=
  recode (IsCPDerivation.ax (pair 4 1 2) sound160 (pairMem 4 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line162 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history162 : List L := line162 :: history161
theorem sound162 : IsCPDerivation F history162 :=
  recode (IsCPDerivation.ax (pair 4 1 3) sound161 (pairMem 4 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line163 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history163 : List L := line163 :: history162
theorem sound163 : IsCPDerivation F history163 :=
  recode (IsCPDerivation.ax (pair 4 1 4) sound162 (pairMem 4 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line164 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history164 : List L := line164 :: history163
theorem sound164 : IsCPDerivation F history164 :=
  recode (IsCPDerivation.ax (pair 4 1 5) sound163 (pairMem 4 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line165 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history165 : List L := line165 :: history164
theorem sound165 : IsCPDerivation F history165 :=
  recode (IsCPDerivation.ax (pair 4 2 3) sound164 (pairMem 4 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line166 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history166 : List L := line166 :: history165
theorem sound166 : IsCPDerivation F history166 :=
  recode (IsCPDerivation.ax (pair 4 2 4) sound165 (pairMem 4 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line167 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history167 : List L := line167 :: history166
theorem sound167 : IsCPDerivation F history167 :=
  recode (IsCPDerivation.ax (pair 4 2 5) sound166 (pairMem 4 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line168 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history168 : List L := line168 :: history167
theorem sound168 : IsCPDerivation F history168 :=
  recode (IsCPDerivation.ax (pair 4 3 4) sound167 (pairMem 4 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line169 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history169 : List L := line169 :: history168
theorem sound169 : IsCPDerivation F history169 :=
  recode (IsCPDerivation.ax (pair 4 3 5) sound168 (pairMem 4 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line170 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1] (-1)
def history170 : List L := line170 :: history169
theorem sound170 : IsCPDerivation F history170 :=
  recode (IsCPDerivation.ax (pair 4 4 5) sound169 (pairMem 4 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line171 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history171 : List L := line171 :: history170
theorem sound171 : IsCPDerivation F history171 :=
  recode (IsCPDerivation.add (e := line156) (e' := line157) sound170 (earlier history170 14 (by decide)) (earlier history170 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line172 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history172 : List L := line172 :: history171
theorem sound172 : IsCPDerivation F history172 :=
  recode (IsCPDerivation.add (e := line171) (e' := line161) sound171 (earlier history171 0 (by decide)) (earlier history171 10 (by decide))) (by decide +kernel) (by decide +kernel)

def line173 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history173 : List L := line173 :: history172
theorem sound173 : IsCPDerivation F history173 :=
  recode (IsCPDerivation.div (e := line172) 2 sound172 (earlier history172 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line174 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-2)
def history174 : List L := line174 :: history173
theorem sound174 : IsCPDerivation F history174 :=
  recode (IsCPDerivation.add (e := line158) (e' := line159) sound173 (earlier history173 15 (by decide)) (earlier history173 14 (by decide))) (by decide +kernel) (by decide +kernel)

def line175 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0] (-3)
def history175 : List L := line175 :: history174
theorem sound175 : IsCPDerivation F history175 :=
  recode (IsCPDerivation.add (e := line174) (e' := line168) sound174 (earlier history174 0 (by decide)) (earlier history174 6 (by decide))) (by decide +kernel) (by decide +kernel)

def line176 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history176 : List L := line176 :: history175
theorem sound176 : IsCPDerivation F history176 :=
  recode (IsCPDerivation.div (e := line175) 2 sound175 (earlier history175 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line177 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-2)
def history177 : List L := line177 :: history176
theorem sound177 : IsCPDerivation F history177 :=
  recode (IsCPDerivation.add (e := line162) (e' := line163) sound176 (earlier history176 14 (by decide)) (earlier history176 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line178 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0] (-3)
def history178 : List L := line178 :: history177
theorem sound178 : IsCPDerivation F history178 :=
  recode (IsCPDerivation.add (e := line177) (e' := line168) sound177 (earlier history177 0 (by decide)) (earlier history177 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line179 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history179 : List L := line179 :: history178
theorem sound179 : IsCPDerivation F history179 :=
  recode (IsCPDerivation.div (e := line178) 2 sound178 (earlier history178 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line180 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-2)
def history180 : List L := line180 :: history179
theorem sound180 : IsCPDerivation F history180 :=
  recode (IsCPDerivation.add (e := line165) (e' := line166) sound179 (earlier history179 14 (by decide)) (earlier history179 13 (by decide))) (by decide +kernel) (by decide +kernel)

def line181 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0] (-3)
def history181 : List L := line181 :: history180
theorem sound181 : IsCPDerivation F history181 :=
  recode (IsCPDerivation.add (e := line180) (e' := line168) sound180 (earlier history180 0 (by decide)) (earlier history180 12 (by decide))) (by decide +kernel) (by decide +kernel)

def line182 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history182 : List L := line182 :: history181
theorem sound182 : IsCPDerivation F history182 :=
  recode (IsCPDerivation.div (e := line181) 2 sound181 (earlier history181 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line183 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history183 : List L := line183 :: history182
theorem sound183 : IsCPDerivation F history183 :=
  recode (IsCPDerivation.mul (e := line173) 2 sound182 (earlier history182 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line184 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-3)
def history184 : List L := line184 :: history183
theorem sound184 : IsCPDerivation F history184 :=
  recode (IsCPDerivation.add (e := line183) (e' := line176) sound183 (earlier history183 0 (by decide)) (earlier history183 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line185 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0] (-4)
def history185 : List L := line185 :: history184
theorem sound185 : IsCPDerivation F history185 :=
  recode (IsCPDerivation.add (e := line184) (e' := line179) sound184 (earlier history184 0 (by decide)) (earlier history184 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line186 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0] (-5)
def history186 : List L := line186 :: history185
theorem sound186 : IsCPDerivation F history186 :=
  recode (IsCPDerivation.add (e := line185) (e' := line182) sound185 (earlier history185 0 (by decide)) (earlier history185 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line187 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history187 : List L := line187 :: history186
theorem sound187 : IsCPDerivation F history187 :=
  recode (IsCPDerivation.div (e := line186) 3 sound186 (earlier history186 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line188 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0] (-4)
def history188 : List L := line188 :: history187
theorem sound188 : IsCPDerivation F history188 :=
  recode (IsCPDerivation.mul (e := line187) 4 sound187 (earlier history187 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line189 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1] (-5)
def history189 : List L := line189 :: history188
theorem sound189 : IsCPDerivation F history189 :=
  recode (IsCPDerivation.add (e := line188) (e' := line160) sound188 (earlier history188 0 (by decide)) (earlier history188 28 (by decide))) (by decide +kernel) (by decide +kernel)

def line190 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2] (-6)
def history190 : List L := line190 :: history189
theorem sound190 : IsCPDerivation F history190 :=
  recode (IsCPDerivation.add (e := line189) (e' := line164) sound189 (earlier history189 0 (by decide)) (earlier history189 25 (by decide))) (by decide +kernel) (by decide +kernel)

def line191 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3] (-7)
def history191 : List L := line191 :: history190
theorem sound191 : IsCPDerivation F history191 :=
  recode (IsCPDerivation.add (e := line190) (e' := line167) sound190 (earlier history190 0 (by decide)) (earlier history190 23 (by decide))) (by decide +kernel) (by decide +kernel)

def line192 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4] (-8)
def history192 : List L := line192 :: history191
theorem sound192 : IsCPDerivation F history192 :=
  recode (IsCPDerivation.add (e := line191) (e' := line169) sound191 (earlier history191 0 (by decide)) (earlier history191 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line193 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5] (-9)
def history193 : List L := line193 :: history192
theorem sound193 : IsCPDerivation F history193 :=
  recode (IsCPDerivation.add (e := line192) (e' := line170) sound192 (earlier history192 0 (by decide)) (earlier history192 22 (by decide))) (by decide +kernel) (by decide +kernel)

def line194 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1] (-1)
def history194 : List L := line194 :: history193
theorem sound194 : IsCPDerivation F history194 :=
  recode (IsCPDerivation.div (e := line193) 5 sound193 (earlier history193 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line195 : L := dataLine [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history195 : List L := line195 :: history194
theorem sound195 : IsCPDerivation F history195 :=
  recode (IsCPDerivation.ax (pigeon 0) sound194 (pigeonMem 0)) (by decide +kernel) (by decide +kernel)

def line196 : L := dataLine [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history196 : List L := line196 :: history195
theorem sound196 : IsCPDerivation F history196 :=
  recode (IsCPDerivation.ax (pigeon 1) sound195 (pigeonMem 1)) (by decide +kernel) (by decide +kernel)

def line197 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history197 : List L := line197 :: history196
theorem sound197 : IsCPDerivation F history197 :=
  recode (IsCPDerivation.ax (pigeon 2) sound196 (pigeonMem 2)) (by decide +kernel) (by decide +kernel)

def line198 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history198 : List L := line198 :: history197
theorem sound198 : IsCPDerivation F history198 :=
  recode (IsCPDerivation.ax (pigeon 3) sound197 (pigeonMem 3)) (by decide +kernel) (by decide +kernel)

def line199 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0] (1)
def history199 : List L := line199 :: history198
theorem sound199 : IsCPDerivation F history199 :=
  recode (IsCPDerivation.ax (pigeon 4) sound198 (pigeonMem 4)) (by decide +kernel) (by decide +kernel)

def line200 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] (1)
def history200 : List L := line200 :: history199
theorem sound200 : IsCPDerivation F history200 :=
  recode (IsCPDerivation.ax (pigeon 5) sound199 (pigeonMem 5)) (by decide +kernel) (by decide +kernel)

def line201 : L := dataLine [-1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0] (-2)
def history201 : List L := line201 :: history200
theorem sound201 : IsCPDerivation F history201 :=
  recode (IsCPDerivation.add (e := line38) (e' := line77) sound200 (earlier history200 162 (by decide)) (earlier history200 123 (by decide))) (by decide +kernel) (by decide +kernel)

def line202 : L := dataLine [-1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0] (-3)
def history202 : List L := line202 :: history201
theorem sound202 : IsCPDerivation F history202 :=
  recode (IsCPDerivation.add (e := line201) (e' := line116) sound201 (earlier history201 0 (by decide)) (earlier history201 85 (by decide))) (by decide +kernel) (by decide +kernel)

def line203 : L := dataLine [-1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0] (-4)
def history203 : List L := line203 :: history202
theorem sound203 : IsCPDerivation F history203 :=
  recode (IsCPDerivation.add (e := line202) (e' := line155) sound202 (earlier history202 0 (by decide)) (earlier history202 47 (by decide))) (by decide +kernel) (by decide +kernel)

def line204 : L := dataLine [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-5)
def history204 : List L := line204 :: history203
theorem sound204 : IsCPDerivation F history204 :=
  recode (IsCPDerivation.add (e := line203) (e' := line194) sound203 (earlier history203 0 (by decide)) (earlier history203 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line205 : L := dataLine [0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-4)
def history205 : List L := line205 :: history204
theorem sound205 : IsCPDerivation F history205 :=
  recode (IsCPDerivation.add (e := line204) (e' := line195) sound204 (earlier history204 0 (by decide)) (earlier history204 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line206 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-3)
def history206 : List L := line206 :: history205
theorem sound206 : IsCPDerivation F history206 :=
  recode (IsCPDerivation.add (e := line205) (e' := line196) sound205 (earlier history205 0 (by decide)) (earlier history205 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line207 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-2)
def history207 : List L := line207 :: history206
theorem sound207 : IsCPDerivation F history207 :=
  recode (IsCPDerivation.add (e := line206) (e' := line197) sound206 (earlier history206 0 (by decide)) (earlier history206 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line208 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-1)
def history208 : List L := line208 :: history207
theorem sound208 : IsCPDerivation F history208 :=
  recode (IsCPDerivation.add (e := line207) (e' := line198) sound207 (earlier history207 0 (by decide)) (earlier history207 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line209 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1] (0)
def history209 : List L := line209 :: history208
theorem sound209 : IsCPDerivation F history209 :=
  recode (IsCPDerivation.add (e := line208) (e' := line199) sound208 (earlier history208 0 (by decide)) (earlier history208 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line210 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history210 : List L := line210 :: history209
theorem sound210 : IsCPDerivation F history210 :=
  recode (IsCPDerivation.add (e := line209) (e' := line200) sound209 (earlier history209 0 (by decide)) (earlier history209 9 (by decide))) (by decide +kernel) (by decide +kernel)

theorem certificate : ∃ π : List L, IsCPRefutation F π ∧ π.length = 211 := by
  have eq : line210 = ((0 : V → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) rfl
  refine ⟨history210, ⟨sound210, ?_⟩, rfl⟩
  rw [← eq]
  exact earlier history210 0 (by decide)

end PEqualNP.Outside.L_meta_9708.DepthThree
