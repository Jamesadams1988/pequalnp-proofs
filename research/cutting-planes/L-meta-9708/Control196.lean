import PEqualNP.Defs

set_option maxRecDepth 4096

namespace PEqualNP.Outside.L_meta_9708.Certificate
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

def line2 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history2 : List L := line2 :: history1
theorem sound2 : IsCPDerivation F history2 :=
  recode (IsCPDerivation.ax (pair 0 1 2) sound1 (pairMem 0 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line3 : L := dataLine [-2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history3 : List L := line3 :: history2
theorem sound3 : IsCPDerivation F history3 :=
  recode (IsCPDerivation.add (e := line0) (e' := line1) sound2 (earlier history2 2 (by decide)) (earlier history2 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line4 : L := dataLine [-2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history4 : List L := line4 :: history3
theorem sound4 : IsCPDerivation F history4 :=
  recode (IsCPDerivation.add (e := line3) (e' := line2) sound3 (earlier history3 0 (by decide)) (earlier history3 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line5 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history5 : List L := line5 :: history4
theorem sound5 : IsCPDerivation F history5 :=
  recode (IsCPDerivation.div (e := line4) 2 sound4 (earlier history4 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line6 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history6 : List L := line6 :: history5
theorem sound6 : IsCPDerivation F history6 :=
  recode (IsCPDerivation.ax (pair 0 0 3) sound5 (pairMem 0 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line7 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history7 : List L := line7 :: history6
theorem sound7 : IsCPDerivation F history7 :=
  recode (IsCPDerivation.ax (pair 0 1 3) sound6 (pairMem 0 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line8 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history8 : List L := line8 :: history7
theorem sound8 : IsCPDerivation F history8 :=
  recode (IsCPDerivation.ax (pair 0 2 3) sound7 (pairMem 0 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line9 : L := dataLine [-2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history9 : List L := line9 :: history8
theorem sound9 : IsCPDerivation F history9 :=
  recode (IsCPDerivation.mul (e := line5) 2 sound8 (earlier history8 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line10 : L := dataLine [-3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history10 : List L := line10 :: history9
theorem sound10 : IsCPDerivation F history10 :=
  recode (IsCPDerivation.add (e := line9) (e' := line6) sound9 (earlier history9 0 (by decide)) (earlier history9 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line11 : L := dataLine [-3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history11 : List L := line11 :: history10
theorem sound11 : IsCPDerivation F history11 :=
  recode (IsCPDerivation.add (e := line10) (e' := line7) sound10 (earlier history10 0 (by decide)) (earlier history10 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line12 : L := dataLine [-3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history12 : List L := line12 :: history11
theorem sound12 : IsCPDerivation F history12 :=
  recode (IsCPDerivation.add (e := line11) (e' := line8) sound11 (earlier history11 0 (by decide)) (earlier history11 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line13 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history13 : List L := line13 :: history12
theorem sound13 : IsCPDerivation F history13 :=
  recode (IsCPDerivation.div (e := line12) 3 sound12 (earlier history12 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line14 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history14 : List L := line14 :: history13
theorem sound14 : IsCPDerivation F history14 :=
  recode (IsCPDerivation.ax (pair 0 0 4) sound13 (pairMem 0 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line15 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history15 : List L := line15 :: history14
theorem sound15 : IsCPDerivation F history15 :=
  recode (IsCPDerivation.ax (pair 0 1 4) sound14 (pairMem 0 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line16 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history16 : List L := line16 :: history15
theorem sound16 : IsCPDerivation F history16 :=
  recode (IsCPDerivation.ax (pair 0 2 4) sound15 (pairMem 0 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line17 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history17 : List L := line17 :: history16
theorem sound17 : IsCPDerivation F history17 :=
  recode (IsCPDerivation.ax (pair 0 3 4) sound16 (pairMem 0 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line18 : L := dataLine [-3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history18 : List L := line18 :: history17
theorem sound18 : IsCPDerivation F history18 :=
  recode (IsCPDerivation.mul (e := line13) 3 sound17 (earlier history17 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line19 : L := dataLine [-4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history19 : List L := line19 :: history18
theorem sound19 : IsCPDerivation F history19 :=
  recode (IsCPDerivation.add (e := line18) (e' := line14) sound18 (earlier history18 0 (by decide)) (earlier history18 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line20 : L := dataLine [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history20 : List L := line20 :: history19
theorem sound20 : IsCPDerivation F history20 :=
  recode (IsCPDerivation.add (e := line19) (e' := line15) sound19 (earlier history19 0 (by decide)) (earlier history19 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line21 : L := dataLine [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-6)
def history21 : List L := line21 :: history20
theorem sound21 : IsCPDerivation F history21 :=
  recode (IsCPDerivation.add (e := line20) (e' := line16) sound20 (earlier history20 0 (by decide)) (earlier history20 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line22 : L := dataLine [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-7)
def history22 : List L := line22 :: history21
theorem sound22 : IsCPDerivation F history22 :=
  recode (IsCPDerivation.add (e := line21) (e' := line17) sound21 (earlier history21 0 (by decide)) (earlier history21 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line23 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history23 : List L := line23 :: history22
theorem sound23 : IsCPDerivation F history23 :=
  recode (IsCPDerivation.div (e := line22) 4 sound22 (earlier history22 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line24 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history24 : List L := line24 :: history23
theorem sound24 : IsCPDerivation F history24 :=
  recode (IsCPDerivation.ax (pair 0 0 5) sound23 (pairMem 0 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line25 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history25 : List L := line25 :: history24
theorem sound25 : IsCPDerivation F history25 :=
  recode (IsCPDerivation.ax (pair 0 1 5) sound24 (pairMem 0 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line26 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history26 : List L := line26 :: history25
theorem sound26 : IsCPDerivation F history26 :=
  recode (IsCPDerivation.ax (pair 0 2 5) sound25 (pairMem 0 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line27 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history27 : List L := line27 :: history26
theorem sound27 : IsCPDerivation F history27 :=
  recode (IsCPDerivation.ax (pair 0 3 5) sound26 (pairMem 0 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line28 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history28 : List L := line28 :: history27
theorem sound28 : IsCPDerivation F history28 :=
  recode (IsCPDerivation.ax (pair 0 4 5) sound27 (pairMem 0 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line29 : L := dataLine [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history29 : List L := line29 :: history28
theorem sound29 : IsCPDerivation F history29 :=
  recode (IsCPDerivation.mul (e := line23) 4 sound28 (earlier history28 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line30 : L := dataLine [-5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-5)
def history30 : List L := line30 :: history29
theorem sound30 : IsCPDerivation F history30 :=
  recode (IsCPDerivation.add (e := line29) (e' := line24) sound29 (earlier history29 0 (by decide)) (earlier history29 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line31 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0, 0] (-6)
def history31 : List L := line31 :: history30
theorem sound31 : IsCPDerivation F history31 :=
  recode (IsCPDerivation.add (e := line30) (e' := line25) sound30 (earlier history30 0 (by decide)) (earlier history30 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line32 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0] (-7)
def history32 : List L := line32 :: history31
theorem sound32 : IsCPDerivation F history32 :=
  recode (IsCPDerivation.add (e := line31) (e' := line26) sound31 (earlier history31 0 (by decide)) (earlier history31 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line33 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0] (-8)
def history33 : List L := line33 :: history32
theorem sound33 : IsCPDerivation F history33 :=
  recode (IsCPDerivation.add (e := line32) (e' := line27) sound32 (earlier history32 0 (by decide)) (earlier history32 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line34 : L := dataLine [-5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0] (-9)
def history34 : List L := line34 :: history33
theorem sound34 : IsCPDerivation F history34 :=
  recode (IsCPDerivation.add (e := line33) (e' := line28) sound33 (earlier history33 0 (by decide)) (earlier history33 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line35 : L := dataLine [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history35 : List L := line35 :: history34
theorem sound35 : IsCPDerivation F history35 :=
  recode (IsCPDerivation.div (e := line34) 5 sound34 (earlier history34 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line36 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history36 : List L := line36 :: history35
theorem sound36 : IsCPDerivation F history36 :=
  recode (IsCPDerivation.ax (pair 1 0 1) sound35 (pairMem 1 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line37 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history37 : List L := line37 :: history36
theorem sound37 : IsCPDerivation F history37 :=
  recode (IsCPDerivation.ax (pair 1 0 2) sound36 (pairMem 1 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line38 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history38 : List L := line38 :: history37
theorem sound38 : IsCPDerivation F history38 :=
  recode (IsCPDerivation.ax (pair 1 1 2) sound37 (pairMem 1 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line39 : L := dataLine [0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history39 : List L := line39 :: history38
theorem sound39 : IsCPDerivation F history39 :=
  recode (IsCPDerivation.add (e := line36) (e' := line37) sound38 (earlier history38 2 (by decide)) (earlier history38 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line40 : L := dataLine [0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history40 : List L := line40 :: history39
theorem sound40 : IsCPDerivation F history40 :=
  recode (IsCPDerivation.add (e := line39) (e' := line38) sound39 (earlier history39 0 (by decide)) (earlier history39 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line41 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history41 : List L := line41 :: history40
theorem sound41 : IsCPDerivation F history41 :=
  recode (IsCPDerivation.div (e := line40) 2 sound40 (earlier history40 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line42 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history42 : List L := line42 :: history41
theorem sound42 : IsCPDerivation F history42 :=
  recode (IsCPDerivation.ax (pair 1 0 3) sound41 (pairMem 1 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line43 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history43 : List L := line43 :: history42
theorem sound43 : IsCPDerivation F history43 :=
  recode (IsCPDerivation.ax (pair 1 1 3) sound42 (pairMem 1 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line44 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history44 : List L := line44 :: history43
theorem sound44 : IsCPDerivation F history44 :=
  recode (IsCPDerivation.ax (pair 1 2 3) sound43 (pairMem 1 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line45 : L := dataLine [0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history45 : List L := line45 :: history44
theorem sound45 : IsCPDerivation F history45 :=
  recode (IsCPDerivation.mul (e := line41) 2 sound44 (earlier history44 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line46 : L := dataLine [0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history46 : List L := line46 :: history45
theorem sound46 : IsCPDerivation F history46 :=
  recode (IsCPDerivation.add (e := line45) (e' := line42) sound45 (earlier history45 0 (by decide)) (earlier history45 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line47 : L := dataLine [0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history47 : List L := line47 :: history46
theorem sound47 : IsCPDerivation F history47 :=
  recode (IsCPDerivation.add (e := line46) (e' := line43) sound46 (earlier history46 0 (by decide)) (earlier history46 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line48 : L := dataLine [0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history48 : List L := line48 :: history47
theorem sound48 : IsCPDerivation F history48 :=
  recode (IsCPDerivation.add (e := line47) (e' := line44) sound47 (earlier history47 0 (by decide)) (earlier history47 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line49 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history49 : List L := line49 :: history48
theorem sound49 : IsCPDerivation F history49 :=
  recode (IsCPDerivation.div (e := line48) 3 sound48 (earlier history48 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line50 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history50 : List L := line50 :: history49
theorem sound50 : IsCPDerivation F history50 :=
  recode (IsCPDerivation.ax (pair 1 0 4) sound49 (pairMem 1 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line51 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history51 : List L := line51 :: history50
theorem sound51 : IsCPDerivation F history51 :=
  recode (IsCPDerivation.ax (pair 1 1 4) sound50 (pairMem 1 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line52 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history52 : List L := line52 :: history51
theorem sound52 : IsCPDerivation F history52 :=
  recode (IsCPDerivation.ax (pair 1 2 4) sound51 (pairMem 1 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line53 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history53 : List L := line53 :: history52
theorem sound53 : IsCPDerivation F history53 :=
  recode (IsCPDerivation.ax (pair 1 3 4) sound52 (pairMem 1 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line54 : L := dataLine [0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history54 : List L := line54 :: history53
theorem sound54 : IsCPDerivation F history54 :=
  recode (IsCPDerivation.mul (e := line49) 3 sound53 (earlier history53 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line55 : L := dataLine [0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history55 : List L := line55 :: history54
theorem sound55 : IsCPDerivation F history55 :=
  recode (IsCPDerivation.add (e := line54) (e' := line50) sound54 (earlier history54 0 (by decide)) (earlier history54 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line56 : L := dataLine [0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history56 : List L := line56 :: history55
theorem sound56 : IsCPDerivation F history56 :=
  recode (IsCPDerivation.add (e := line55) (e' := line51) sound55 (earlier history55 0 (by decide)) (earlier history55 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line57 : L := dataLine [0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0] (-6)
def history57 : List L := line57 :: history56
theorem sound57 : IsCPDerivation F history57 :=
  recode (IsCPDerivation.add (e := line56) (e' := line52) sound56 (earlier history56 0 (by decide)) (earlier history56 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line58 : L := dataLine [0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0] (-7)
def history58 : List L := line58 :: history57
theorem sound58 : IsCPDerivation F history58 :=
  recode (IsCPDerivation.add (e := line57) (e' := line53) sound57 (earlier history57 0 (by decide)) (earlier history57 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line59 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history59 : List L := line59 :: history58
theorem sound59 : IsCPDerivation F history59 :=
  recode (IsCPDerivation.div (e := line58) 4 sound58 (earlier history58 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line60 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history60 : List L := line60 :: history59
theorem sound60 : IsCPDerivation F history60 :=
  recode (IsCPDerivation.ax (pair 1 0 5) sound59 (pairMem 1 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line61 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history61 : List L := line61 :: history60
theorem sound61 : IsCPDerivation F history61 :=
  recode (IsCPDerivation.ax (pair 1 1 5) sound60 (pairMem 1 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line62 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history62 : List L := line62 :: history61
theorem sound62 : IsCPDerivation F history62 :=
  recode (IsCPDerivation.ax (pair 1 2 5) sound61 (pairMem 1 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line63 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history63 : List L := line63 :: history62
theorem sound63 : IsCPDerivation F history63 :=
  recode (IsCPDerivation.ax (pair 1 3 5) sound62 (pairMem 1 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line64 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history64 : List L := line64 :: history63
theorem sound64 : IsCPDerivation F history64 :=
  recode (IsCPDerivation.ax (pair 1 4 5) sound63 (pairMem 1 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line65 : L := dataLine [0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history65 : List L := line65 :: history64
theorem sound65 : IsCPDerivation F history65 :=
  recode (IsCPDerivation.mul (e := line59) 4 sound64 (earlier history64 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line66 : L := dataLine [0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0] (-5)
def history66 : List L := line66 :: history65
theorem sound66 : IsCPDerivation F history66 :=
  recode (IsCPDerivation.add (e := line65) (e' := line60) sound65 (earlier history65 0 (by decide)) (earlier history65 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line67 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0] (-6)
def history67 : List L := line67 :: history66
theorem sound67 : IsCPDerivation F history67 :=
  recode (IsCPDerivation.add (e := line66) (e' := line61) sound66 (earlier history66 0 (by decide)) (earlier history66 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line68 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0] (-7)
def history68 : List L := line68 :: history67
theorem sound68 : IsCPDerivation F history68 :=
  recode (IsCPDerivation.add (e := line67) (e' := line62) sound67 (earlier history67 0 (by decide)) (earlier history67 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line69 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0] (-8)
def history69 : List L := line69 :: history68
theorem sound69 : IsCPDerivation F history69 :=
  recode (IsCPDerivation.add (e := line68) (e' := line63) sound68 (earlier history68 0 (by decide)) (earlier history68 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line70 : L := dataLine [0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0] (-9)
def history70 : List L := line70 :: history69
theorem sound70 : IsCPDerivation F history70 :=
  recode (IsCPDerivation.add (e := line69) (e' := line64) sound69 (earlier history69 0 (by decide)) (earlier history69 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line71 : L := dataLine [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history71 : List L := line71 :: history70
theorem sound71 : IsCPDerivation F history71 :=
  recode (IsCPDerivation.div (e := line70) 5 sound70 (earlier history70 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line72 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history72 : List L := line72 :: history71
theorem sound72 : IsCPDerivation F history72 :=
  recode (IsCPDerivation.ax (pair 2 0 1) sound71 (pairMem 2 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line73 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history73 : List L := line73 :: history72
theorem sound73 : IsCPDerivation F history73 :=
  recode (IsCPDerivation.ax (pair 2 0 2) sound72 (pairMem 2 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line74 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history74 : List L := line74 :: history73
theorem sound74 : IsCPDerivation F history74 :=
  recode (IsCPDerivation.ax (pair 2 1 2) sound73 (pairMem 2 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line75 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history75 : List L := line75 :: history74
theorem sound75 : IsCPDerivation F history75 :=
  recode (IsCPDerivation.add (e := line72) (e' := line73) sound74 (earlier history74 2 (by decide)) (earlier history74 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line76 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history76 : List L := line76 :: history75
theorem sound76 : IsCPDerivation F history76 :=
  recode (IsCPDerivation.add (e := line75) (e' := line74) sound75 (earlier history75 0 (by decide)) (earlier history75 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line77 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history77 : List L := line77 :: history76
theorem sound77 : IsCPDerivation F history77 :=
  recode (IsCPDerivation.div (e := line76) 2 sound76 (earlier history76 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line78 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history78 : List L := line78 :: history77
theorem sound78 : IsCPDerivation F history78 :=
  recode (IsCPDerivation.ax (pair 2 0 3) sound77 (pairMem 2 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line79 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history79 : List L := line79 :: history78
theorem sound79 : IsCPDerivation F history79 :=
  recode (IsCPDerivation.ax (pair 2 1 3) sound78 (pairMem 2 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line80 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history80 : List L := line80 :: history79
theorem sound80 : IsCPDerivation F history80 :=
  recode (IsCPDerivation.ax (pair 2 2 3) sound79 (pairMem 2 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line81 : L := dataLine [0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history81 : List L := line81 :: history80
theorem sound81 : IsCPDerivation F history81 :=
  recode (IsCPDerivation.mul (e := line77) 2 sound80 (earlier history80 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line82 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history82 : List L := line82 :: history81
theorem sound82 : IsCPDerivation F history82 :=
  recode (IsCPDerivation.add (e := line81) (e' := line78) sound81 (earlier history81 0 (by decide)) (earlier history81 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line83 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history83 : List L := line83 :: history82
theorem sound83 : IsCPDerivation F history83 :=
  recode (IsCPDerivation.add (e := line82) (e' := line79) sound82 (earlier history82 0 (by decide)) (earlier history82 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line84 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history84 : List L := line84 :: history83
theorem sound84 : IsCPDerivation F history84 :=
  recode (IsCPDerivation.add (e := line83) (e' := line80) sound83 (earlier history83 0 (by decide)) (earlier history83 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line85 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history85 : List L := line85 :: history84
theorem sound85 : IsCPDerivation F history85 :=
  recode (IsCPDerivation.div (e := line84) 3 sound84 (earlier history84 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line86 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history86 : List L := line86 :: history85
theorem sound86 : IsCPDerivation F history86 :=
  recode (IsCPDerivation.ax (pair 2 0 4) sound85 (pairMem 2 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line87 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history87 : List L := line87 :: history86
theorem sound87 : IsCPDerivation F history87 :=
  recode (IsCPDerivation.ax (pair 2 1 4) sound86 (pairMem 2 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line88 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history88 : List L := line88 :: history87
theorem sound88 : IsCPDerivation F history88 :=
  recode (IsCPDerivation.ax (pair 2 2 4) sound87 (pairMem 2 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line89 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history89 : List L := line89 :: history88
theorem sound89 : IsCPDerivation F history89 :=
  recode (IsCPDerivation.ax (pair 2 3 4) sound88 (pairMem 2 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line90 : L := dataLine [0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history90 : List L := line90 :: history89
theorem sound90 : IsCPDerivation F history90 :=
  recode (IsCPDerivation.mul (e := line85) 3 sound89 (earlier history89 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line91 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-4)
def history91 : List L := line91 :: history90
theorem sound91 : IsCPDerivation F history91 :=
  recode (IsCPDerivation.add (e := line90) (e' := line86) sound90 (earlier history90 0 (by decide)) (earlier history90 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line92 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] (-5)
def history92 : List L := line92 :: history91
theorem sound92 : IsCPDerivation F history92 :=
  recode (IsCPDerivation.add (e := line91) (e' := line87) sound91 (earlier history91 0 (by decide)) (earlier history91 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line93 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0] (-6)
def history93 : List L := line93 :: history92
theorem sound93 : IsCPDerivation F history93 :=
  recode (IsCPDerivation.add (e := line92) (e' := line88) sound92 (earlier history92 0 (by decide)) (earlier history92 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line94 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0] (-7)
def history94 : List L := line94 :: history93
theorem sound94 : IsCPDerivation F history94 :=
  recode (IsCPDerivation.add (e := line93) (e' := line89) sound93 (earlier history93 0 (by decide)) (earlier history93 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line95 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history95 : List L := line95 :: history94
theorem sound95 : IsCPDerivation F history95 :=
  recode (IsCPDerivation.div (e := line94) 4 sound94 (earlier history94 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line96 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history96 : List L := line96 :: history95
theorem sound96 : IsCPDerivation F history96 :=
  recode (IsCPDerivation.ax (pair 2 0 5) sound95 (pairMem 2 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line97 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history97 : List L := line97 :: history96
theorem sound97 : IsCPDerivation F history97 :=
  recode (IsCPDerivation.ax (pair 2 1 5) sound96 (pairMem 2 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line98 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history98 : List L := line98 :: history97
theorem sound98 : IsCPDerivation F history98 :=
  recode (IsCPDerivation.ax (pair 2 2 5) sound97 (pairMem 2 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line99 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history99 : List L := line99 :: history98
theorem sound99 : IsCPDerivation F history99 :=
  recode (IsCPDerivation.ax (pair 2 3 5) sound98 (pairMem 2 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line100 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0] (-1)
def history100 : List L := line100 :: history99
theorem sound100 : IsCPDerivation F history100 :=
  recode (IsCPDerivation.ax (pair 2 4 5) sound99 (pairMem 2 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line101 : L := dataLine [0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0] (-4)
def history101 : List L := line101 :: history100
theorem sound101 : IsCPDerivation F history101 :=
  recode (IsCPDerivation.mul (e := line95) 4 sound100 (earlier history100 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line102 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0] (-5)
def history102 : List L := line102 :: history101
theorem sound102 : IsCPDerivation F history102 :=
  recode (IsCPDerivation.add (e := line101) (e' := line96) sound101 (earlier history101 0 (by decide)) (earlier history101 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line103 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0] (-6)
def history103 : List L := line103 :: history102
theorem sound103 : IsCPDerivation F history103 :=
  recode (IsCPDerivation.add (e := line102) (e' := line97) sound102 (earlier history102 0 (by decide)) (earlier history102 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line104 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0] (-7)
def history104 : List L := line104 :: history103
theorem sound104 : IsCPDerivation F history104 :=
  recode (IsCPDerivation.add (e := line103) (e' := line98) sound103 (earlier history103 0 (by decide)) (earlier history103 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line105 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0] (-8)
def history105 : List L := line105 :: history104
theorem sound105 : IsCPDerivation F history105 :=
  recode (IsCPDerivation.add (e := line104) (e' := line99) sound104 (earlier history104 0 (by decide)) (earlier history104 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line106 : L := dataLine [0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0] (-9)
def history106 : List L := line106 :: history105
theorem sound106 : IsCPDerivation F history106 :=
  recode (IsCPDerivation.add (e := line105) (e' := line100) sound105 (earlier history105 0 (by decide)) (earlier history105 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line107 : L := dataLine [0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0] (-1)
def history107 : List L := line107 :: history106
theorem sound107 : IsCPDerivation F history107 :=
  recode (IsCPDerivation.div (e := line106) 5 sound106 (earlier history106 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line108 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history108 : List L := line108 :: history107
theorem sound108 : IsCPDerivation F history108 :=
  recode (IsCPDerivation.ax (pair 3 0 1) sound107 (pairMem 3 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line109 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history109 : List L := line109 :: history108
theorem sound109 : IsCPDerivation F history109 :=
  recode (IsCPDerivation.ax (pair 3 0 2) sound108 (pairMem 3 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line110 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history110 : List L := line110 :: history109
theorem sound110 : IsCPDerivation F history110 :=
  recode (IsCPDerivation.ax (pair 3 1 2) sound109 (pairMem 3 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line111 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history111 : List L := line111 :: history110
theorem sound111 : IsCPDerivation F history111 :=
  recode (IsCPDerivation.add (e := line108) (e' := line109) sound110 (earlier history110 2 (by decide)) (earlier history110 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line112 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history112 : List L := line112 :: history111
theorem sound112 : IsCPDerivation F history112 :=
  recode (IsCPDerivation.add (e := line111) (e' := line110) sound111 (earlier history111 0 (by decide)) (earlier history111 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line113 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history113 : List L := line113 :: history112
theorem sound113 : IsCPDerivation F history113 :=
  recode (IsCPDerivation.div (e := line112) 2 sound112 (earlier history112 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line114 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history114 : List L := line114 :: history113
theorem sound114 : IsCPDerivation F history114 :=
  recode (IsCPDerivation.ax (pair 3 0 3) sound113 (pairMem 3 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line115 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history115 : List L := line115 :: history114
theorem sound115 : IsCPDerivation F history115 :=
  recode (IsCPDerivation.ax (pair 3 1 3) sound114 (pairMem 3 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line116 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history116 : List L := line116 :: history115
theorem sound116 : IsCPDerivation F history116 :=
  recode (IsCPDerivation.ax (pair 3 2 3) sound115 (pairMem 3 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line117 : L := dataLine [0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history117 : List L := line117 :: history116
theorem sound117 : IsCPDerivation F history117 :=
  recode (IsCPDerivation.mul (e := line113) 2 sound116 (earlier history116 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line118 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history118 : List L := line118 :: history117
theorem sound118 : IsCPDerivation F history118 :=
  recode (IsCPDerivation.add (e := line117) (e' := line114) sound117 (earlier history117 0 (by decide)) (earlier history117 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line119 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history119 : List L := line119 :: history118
theorem sound119 : IsCPDerivation F history119 :=
  recode (IsCPDerivation.add (e := line118) (e' := line115) sound118 (earlier history118 0 (by decide)) (earlier history118 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line120 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history120 : List L := line120 :: history119
theorem sound120 : IsCPDerivation F history120 :=
  recode (IsCPDerivation.add (e := line119) (e' := line116) sound119 (earlier history119 0 (by decide)) (earlier history119 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line121 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history121 : List L := line121 :: history120
theorem sound121 : IsCPDerivation F history121 :=
  recode (IsCPDerivation.div (e := line120) 3 sound120 (earlier history120 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line122 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history122 : List L := line122 :: history121
theorem sound122 : IsCPDerivation F history122 :=
  recode (IsCPDerivation.ax (pair 3 0 4) sound121 (pairMem 3 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line123 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history123 : List L := line123 :: history122
theorem sound123 : IsCPDerivation F history123 :=
  recode (IsCPDerivation.ax (pair 3 1 4) sound122 (pairMem 3 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line124 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history124 : List L := line124 :: history123
theorem sound124 : IsCPDerivation F history124 :=
  recode (IsCPDerivation.ax (pair 3 2 4) sound123 (pairMem 3 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line125 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history125 : List L := line125 :: history124
theorem sound125 : IsCPDerivation F history125 :=
  recode (IsCPDerivation.ax (pair 3 3 4) sound124 (pairMem 3 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line126 : L := dataLine [0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history126 : List L := line126 :: history125
theorem sound126 : IsCPDerivation F history126 :=
  recode (IsCPDerivation.mul (e := line121) 3 sound125 (earlier history125 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line127 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-4)
def history127 : List L := line127 :: history126
theorem sound127 : IsCPDerivation F history127 :=
  recode (IsCPDerivation.add (e := line126) (e' := line122) sound126 (earlier history126 0 (by decide)) (earlier history126 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line128 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] (-5)
def history128 : List L := line128 :: history127
theorem sound128 : IsCPDerivation F history128 :=
  recode (IsCPDerivation.add (e := line127) (e' := line123) sound127 (earlier history127 0 (by decide)) (earlier history127 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line129 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0] (-6)
def history129 : List L := line129 :: history128
theorem sound129 : IsCPDerivation F history129 :=
  recode (IsCPDerivation.add (e := line128) (e' := line124) sound128 (earlier history128 0 (by decide)) (earlier history128 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line130 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] (-7)
def history130 : List L := line130 :: history129
theorem sound130 : IsCPDerivation F history130 :=
  recode (IsCPDerivation.add (e := line129) (e' := line125) sound129 (earlier history129 0 (by decide)) (earlier history129 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line131 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history131 : List L := line131 :: history130
theorem sound131 : IsCPDerivation F history131 :=
  recode (IsCPDerivation.div (e := line130) 4 sound130 (earlier history130 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line132 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history132 : List L := line132 :: history131
theorem sound132 : IsCPDerivation F history132 :=
  recode (IsCPDerivation.ax (pair 3 0 5) sound131 (pairMem 3 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line133 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history133 : List L := line133 :: history132
theorem sound133 : IsCPDerivation F history133 :=
  recode (IsCPDerivation.ax (pair 3 1 5) sound132 (pairMem 3 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line134 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history134 : List L := line134 :: history133
theorem sound134 : IsCPDerivation F history134 :=
  recode (IsCPDerivation.ax (pair 3 2 5) sound133 (pairMem 3 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line135 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history135 : List L := line135 :: history134
theorem sound135 : IsCPDerivation F history135 :=
  recode (IsCPDerivation.ax (pair 3 3 5) sound134 (pairMem 3 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line136 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] (-1)
def history136 : List L := line136 :: history135
theorem sound136 : IsCPDerivation F history136 :=
  recode (IsCPDerivation.ax (pair 3 4 5) sound135 (pairMem 3 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line137 : L := dataLine [0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] (-4)
def history137 : List L := line137 :: history136
theorem sound137 : IsCPDerivation F history137 :=
  recode (IsCPDerivation.mul (e := line131) 4 sound136 (earlier history136 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line138 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0] (-5)
def history138 : List L := line138 :: history137
theorem sound138 : IsCPDerivation F history138 :=
  recode (IsCPDerivation.add (e := line137) (e' := line132) sound137 (earlier history137 0 (by decide)) (earlier history137 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line139 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0] (-6)
def history139 : List L := line139 :: history138
theorem sound139 : IsCPDerivation F history139 :=
  recode (IsCPDerivation.add (e := line138) (e' := line133) sound138 (earlier history138 0 (by decide)) (earlier history138 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line140 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0] (-7)
def history140 : List L := line140 :: history139
theorem sound140 : IsCPDerivation F history140 :=
  recode (IsCPDerivation.add (e := line139) (e' := line134) sound139 (earlier history139 0 (by decide)) (earlier history139 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line141 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0] (-8)
def history141 : List L := line141 :: history140
theorem sound141 : IsCPDerivation F history141 :=
  recode (IsCPDerivation.add (e := line140) (e' := line135) sound140 (earlier history140 0 (by decide)) (earlier history140 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line142 : L := dataLine [0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0] (-9)
def history142 : List L := line142 :: history141
theorem sound142 : IsCPDerivation F history142 :=
  recode (IsCPDerivation.add (e := line141) (e' := line136) sound141 (earlier history141 0 (by decide)) (earlier history141 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line143 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0] (-1)
def history143 : List L := line143 :: history142
theorem sound143 : IsCPDerivation F history143 :=
  recode (IsCPDerivation.div (e := line142) 5 sound142 (earlier history142 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line144 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history144 : List L := line144 :: history143
theorem sound144 : IsCPDerivation F history144 :=
  recode (IsCPDerivation.ax (pair 4 0 1) sound143 (pairMem 4 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line145 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history145 : List L := line145 :: history144
theorem sound145 : IsCPDerivation F history145 :=
  recode (IsCPDerivation.ax (pair 4 0 2) sound144 (pairMem 4 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line146 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history146 : List L := line146 :: history145
theorem sound146 : IsCPDerivation F history146 :=
  recode (IsCPDerivation.ax (pair 4 1 2) sound145 (pairMem 4 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line147 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history147 : List L := line147 :: history146
theorem sound147 : IsCPDerivation F history147 :=
  recode (IsCPDerivation.add (e := line144) (e' := line145) sound146 (earlier history146 2 (by decide)) (earlier history146 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line148 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history148 : List L := line148 :: history147
theorem sound148 : IsCPDerivation F history148 :=
  recode (IsCPDerivation.add (e := line147) (e' := line146) sound147 (earlier history147 0 (by decide)) (earlier history147 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line149 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history149 : List L := line149 :: history148
theorem sound149 : IsCPDerivation F history149 :=
  recode (IsCPDerivation.div (e := line148) 2 sound148 (earlier history148 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line150 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history150 : List L := line150 :: history149
theorem sound150 : IsCPDerivation F history150 :=
  recode (IsCPDerivation.ax (pair 4 0 3) sound149 (pairMem 4 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line151 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history151 : List L := line151 :: history150
theorem sound151 : IsCPDerivation F history151 :=
  recode (IsCPDerivation.ax (pair 4 1 3) sound150 (pairMem 4 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line152 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history152 : List L := line152 :: history151
theorem sound152 : IsCPDerivation F history152 :=
  recode (IsCPDerivation.ax (pair 4 2 3) sound151 (pairMem 4 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line153 : L := dataLine [0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-2)
def history153 : List L := line153 :: history152
theorem sound153 : IsCPDerivation F history153 :=
  recode (IsCPDerivation.mul (e := line149) 2 sound152 (earlier history152 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line154 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history154 : List L := line154 :: history153
theorem sound154 : IsCPDerivation F history154 :=
  recode (IsCPDerivation.add (e := line153) (e' := line150) sound153 (earlier history153 0 (by decide)) (earlier history153 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line155 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-4)
def history155 : List L := line155 :: history154
theorem sound155 : IsCPDerivation F history155 :=
  recode (IsCPDerivation.add (e := line154) (e' := line151) sound154 (earlier history154 0 (by decide)) (earlier history154 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line156 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history156 : List L := line156 :: history155
theorem sound156 : IsCPDerivation F history156 :=
  recode (IsCPDerivation.add (e := line155) (e' := line152) sound155 (earlier history155 0 (by decide)) (earlier history155 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line157 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history157 : List L := line157 :: history156
theorem sound157 : IsCPDerivation F history157 :=
  recode (IsCPDerivation.div (e := line156) 3 sound156 (earlier history156 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line158 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history158 : List L := line158 :: history157
theorem sound158 : IsCPDerivation F history158 :=
  recode (IsCPDerivation.ax (pair 4 0 4) sound157 (pairMem 4 0 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line159 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history159 : List L := line159 :: history158
theorem sound159 : IsCPDerivation F history159 :=
  recode (IsCPDerivation.ax (pair 4 1 4) sound158 (pairMem 4 1 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line160 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history160 : List L := line160 :: history159
theorem sound160 : IsCPDerivation F history160 :=
  recode (IsCPDerivation.ax (pair 4 2 4) sound159 (pairMem 4 2 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line161 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history161 : List L := line161 :: history160
theorem sound161 : IsCPDerivation F history161 :=
  recode (IsCPDerivation.ax (pair 4 3 4) sound160 (pairMem 4 3 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line162 : L := dataLine [0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-3)
def history162 : List L := line162 :: history161
theorem sound162 : IsCPDerivation F history162 :=
  recode (IsCPDerivation.mul (e := line157) 3 sound161 (earlier history161 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line163 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-4)
def history163 : List L := line163 :: history162
theorem sound163 : IsCPDerivation F history163 :=
  recode (IsCPDerivation.add (e := line162) (e' := line158) sound162 (earlier history162 0 (by decide)) (earlier history162 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line164 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0] (-5)
def history164 : List L := line164 :: history163
theorem sound164 : IsCPDerivation F history164 :=
  recode (IsCPDerivation.add (e := line163) (e' := line159) sound163 (earlier history163 0 (by decide)) (earlier history163 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line165 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0] (-6)
def history165 : List L := line165 :: history164
theorem sound165 : IsCPDerivation F history165 :=
  recode (IsCPDerivation.add (e := line164) (e' := line160) sound164 (earlier history164 0 (by decide)) (earlier history164 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line166 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0] (-7)
def history166 : List L := line166 :: history165
theorem sound166 : IsCPDerivation F history166 :=
  recode (IsCPDerivation.add (e := line165) (e' := line161) sound165 (earlier history165 0 (by decide)) (earlier history165 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line167 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history167 : List L := line167 :: history166
theorem sound167 : IsCPDerivation F history167 :=
  recode (IsCPDerivation.div (e := line166) 4 sound166 (earlier history166 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line168 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history168 : List L := line168 :: history167
theorem sound168 : IsCPDerivation F history168 :=
  recode (IsCPDerivation.ax (pair 4 0 5) sound167 (pairMem 4 0 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line169 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history169 : List L := line169 :: history168
theorem sound169 : IsCPDerivation F history169 :=
  recode (IsCPDerivation.ax (pair 4 1 5) sound168 (pairMem 4 1 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line170 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history170 : List L := line170 :: history169
theorem sound170 : IsCPDerivation F history170 :=
  recode (IsCPDerivation.ax (pair 4 2 5) sound169 (pairMem 4 2 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line171 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history171 : List L := line171 :: history170
theorem sound171 : IsCPDerivation F history171 :=
  recode (IsCPDerivation.ax (pair 4 3 5) sound170 (pairMem 4 3 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line172 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1] (-1)
def history172 : List L := line172 :: history171
theorem sound172 : IsCPDerivation F history172 :=
  recode (IsCPDerivation.ax (pair 4 4 5) sound171 (pairMem 4 4 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line173 : L := dataLine [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0] (-4)
def history173 : List L := line173 :: history172
theorem sound173 : IsCPDerivation F history173 :=
  recode (IsCPDerivation.mul (e := line167) 4 sound172 (earlier history172 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line174 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1] (-5)
def history174 : List L := line174 :: history173
theorem sound174 : IsCPDerivation F history174 :=
  recode (IsCPDerivation.add (e := line173) (e' := line168) sound173 (earlier history173 0 (by decide)) (earlier history173 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line175 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2] (-6)
def history175 : List L := line175 :: history174
theorem sound175 : IsCPDerivation F history175 :=
  recode (IsCPDerivation.add (e := line174) (e' := line169) sound174 (earlier history174 0 (by decide)) (earlier history174 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line176 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -3] (-7)
def history176 : List L := line176 :: history175
theorem sound176 : IsCPDerivation F history176 :=
  recode (IsCPDerivation.add (e := line175) (e' := line170) sound175 (earlier history175 0 (by decide)) (earlier history175 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line177 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4] (-8)
def history177 : List L := line177 :: history176
theorem sound177 : IsCPDerivation F history177 :=
  recode (IsCPDerivation.add (e := line176) (e' := line171) sound176 (earlier history176 0 (by decide)) (earlier history176 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line178 : L := dataLine [0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5, 0, 0, 0, 0, -5] (-9)
def history178 : List L := line178 :: history177
theorem sound178 : IsCPDerivation F history178 :=
  recode (IsCPDerivation.add (e := line177) (e' := line172) sound177 (earlier history177 0 (by decide)) (earlier history177 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line179 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1] (-1)
def history179 : List L := line179 :: history178
theorem sound179 : IsCPDerivation F history179 :=
  recode (IsCPDerivation.div (e := line178) 5 sound178 (earlier history178 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line180 : L := dataLine [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history180 : List L := line180 :: history179
theorem sound180 : IsCPDerivation F history180 :=
  recode (IsCPDerivation.ax (pigeon 0) sound179 (pigeonMem 0)) (by decide +kernel) (by decide +kernel)

def line181 : L := dataLine [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history181 : List L := line181 :: history180
theorem sound181 : IsCPDerivation F history181 :=
  recode (IsCPDerivation.ax (pigeon 1) sound180 (pigeonMem 1)) (by decide +kernel) (by decide +kernel)

def line182 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history182 : List L := line182 :: history181
theorem sound182 : IsCPDerivation F history182 :=
  recode (IsCPDerivation.ax (pigeon 2) sound181 (pigeonMem 2)) (by decide +kernel) (by decide +kernel)

def line183 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history183 : List L := line183 :: history182
theorem sound183 : IsCPDerivation F history183 :=
  recode (IsCPDerivation.ax (pigeon 3) sound182 (pigeonMem 3)) (by decide +kernel) (by decide +kernel)

def line184 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0] (1)
def history184 : List L := line184 :: history183
theorem sound184 : IsCPDerivation F history184 :=
  recode (IsCPDerivation.ax (pigeon 4) sound183 (pigeonMem 4)) (by decide +kernel) (by decide +kernel)

def line185 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] (1)
def history185 : List L := line185 :: history184
theorem sound185 : IsCPDerivation F history185 :=
  recode (IsCPDerivation.ax (pigeon 5) sound184 (pigeonMem 5)) (by decide +kernel) (by decide +kernel)

def line186 : L := dataLine [-1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0] (-2)
def history186 : List L := line186 :: history185
theorem sound186 : IsCPDerivation F history186 :=
  recode (IsCPDerivation.add (e := line35) (e' := line71) sound185 (earlier history185 150 (by decide)) (earlier history185 114 (by decide))) (by decide +kernel) (by decide +kernel)

def line187 : L := dataLine [-1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0] (-3)
def history187 : List L := line187 :: history186
theorem sound187 : IsCPDerivation F history187 :=
  recode (IsCPDerivation.add (e := line186) (e' := line107) sound186 (earlier history186 0 (by decide)) (earlier history186 79 (by decide))) (by decide +kernel) (by decide +kernel)

def line188 : L := dataLine [-1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, 0] (-4)
def history188 : List L := line188 :: history187
theorem sound188 : IsCPDerivation F history188 :=
  recode (IsCPDerivation.add (e := line187) (e' := line143) sound187 (earlier history187 0 (by decide)) (earlier history187 44 (by decide))) (by decide +kernel) (by decide +kernel)

def line189 : L := dataLine [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-5)
def history189 : List L := line189 :: history188
theorem sound189 : IsCPDerivation F history189 :=
  recode (IsCPDerivation.add (e := line188) (e' := line179) sound188 (earlier history188 0 (by decide)) (earlier history188 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line190 : L := dataLine [0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-4)
def history190 : List L := line190 :: history189
theorem sound190 : IsCPDerivation F history190 :=
  recode (IsCPDerivation.add (e := line189) (e' := line180) sound189 (earlier history189 0 (by decide)) (earlier history189 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line191 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-3)
def history191 : List L := line191 :: history190
theorem sound191 : IsCPDerivation F history191 :=
  recode (IsCPDerivation.add (e := line190) (e' := line181) sound190 (earlier history190 0 (by decide)) (earlier history190 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line192 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-2)
def history192 : List L := line192 :: history191
theorem sound192 : IsCPDerivation F history192 :=
  recode (IsCPDerivation.add (e := line191) (e' := line182) sound191 (earlier history191 0 (by decide)) (earlier history191 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line193 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] (-1)
def history193 : List L := line193 :: history192
theorem sound193 : IsCPDerivation F history193 :=
  recode (IsCPDerivation.add (e := line192) (e' := line183) sound192 (earlier history192 0 (by decide)) (earlier history192 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line194 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1] (0)
def history194 : List L := line194 :: history193
theorem sound194 : IsCPDerivation F history194 :=
  recode (IsCPDerivation.add (e := line193) (e' := line184) sound193 (earlier history193 0 (by decide)) (earlier history193 9 (by decide))) (by decide +kernel) (by decide +kernel)

def line195 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history195 : List L := line195 :: history194
theorem sound195 : IsCPDerivation F history195 :=
  recode (IsCPDerivation.add (e := line194) (e' := line185) sound194 (earlier history194 0 (by decide)) (earlier history194 9 (by decide))) (by decide +kernel) (by decide +kernel)

theorem certificate : ∃ π : List L, IsCPRefutation F π ∧ π.length = 196 := by
  have eq : line195 = ((0 : V → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) rfl
  refine ⟨history195, ⟨sound195, ?_⟩, rfl⟩
  rw [← eq]
  exact earlier history195 0 (by decide)

end PEqualNP.Outside.L_meta_9708.Certificate
