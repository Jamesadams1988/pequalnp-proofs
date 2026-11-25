import PEqualNP.Defs

namespace PHPInterval65
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

def line0 : L := dataLine [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history0 : List L := line0 :: empty
theorem sound0 : IsCPDerivation F history0 :=
  recode (IsCPDerivation.ax (pigeon 0) start (pigeonMem 0)) (by decide +kernel) (by decide +kernel)

def line1 : L := dataLine [0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0] (1)
def history1 : List L := line1 :: history0
theorem sound1 : IsCPDerivation F history1 :=
  recode (IsCPDerivation.ax (pigeon 1) sound0 (pigeonMem 1)) (by decide +kernel) (by decide +kernel)

def line2 : L := dataLine [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0] (1)
def history2 : List L := line2 :: history1
theorem sound2 : IsCPDerivation F history2 :=
  recode (IsCPDerivation.ax (pigeon 2) sound1 (pigeonMem 2)) (by decide +kernel) (by decide +kernel)

def line3 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] (1)
def history3 : List L := line3 :: history2
theorem sound3 : IsCPDerivation F history3 :=
  recode (IsCPDerivation.ax (pigeon 3) sound2 (pigeonMem 3)) (by decide +kernel) (by decide +kernel)

def line4 : L := dataLine [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] (-1)
def history4 : List L := line4 :: history3
theorem sound4 : IsCPDerivation F history4 :=
  recode (IsCPDerivation.ax (pair 1 0 1) sound3 (pairMem 1 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line5 : L := dataLine [0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history5 : List L := line5 :: history4
theorem sound5 : IsCPDerivation F history5 :=
  recode (IsCPDerivation.ax (pair 0 1 2) sound4 (pairMem 0 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line6 : L := dataLine [0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history6 : List L := line6 :: history5
theorem sound6 : IsCPDerivation F history6 :=
  recode (IsCPDerivation.ax (pair 0 1 3) sound5 (pairMem 0 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line7 : L := dataLine [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0] (-1)
def history7 : List L := line7 :: history6
theorem sound7 : IsCPDerivation F history7 :=
  recode (IsCPDerivation.ax (pair 0 2 3) sound6 (pairMem 0 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line8 : L := dataLine [0, 0, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0] (-2)
def history8 : List L := line8 :: history7
theorem sound8 : IsCPDerivation F history8 :=
  recode (IsCPDerivation.add (e := line5) (e' := line6) sound7 (earlier history7 2 (by decide)) (earlier history7 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line9 : L := dataLine [0, 0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0] (-3)
def history9 : List L := line9 :: history8
theorem sound9 : IsCPDerivation F history9 :=
  recode (IsCPDerivation.add (e := line7) (e' := line8) sound8 (earlier history8 1 (by decide)) (earlier history8 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line10 : L := dataLine [0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0] (-1)
def history10 : List L := line10 :: history9
theorem sound10 : IsCPDerivation F history10 :=
  recode (IsCPDerivation.div (e := line9) 2 sound9 (earlier history9 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line11 : L := dataLine [0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0] (-1)
def history11 : List L := line11 :: history10
theorem sound11 : IsCPDerivation F history11 :=
  recode (IsCPDerivation.ax (pair 1 1 2) sound10 (pairMem 1 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line12 : L := dataLine [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0] (-1)
def history12 : List L := line12 :: history11
theorem sound12 : IsCPDerivation F history12 :=
  recode (IsCPDerivation.ax (pair 1 1 3) sound11 (pairMem 1 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line13 : L := dataLine [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0] (-1)
def history13 : List L := line13 :: history12
theorem sound13 : IsCPDerivation F history13 :=
  recode (IsCPDerivation.ax (pair 1 2 3) sound12 (pairMem 1 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line14 : L := dataLine [0, 0, 0, 0, -2, 0, 0, -1, 0, 0, -1, 0] (-2)
def history14 : List L := line14 :: history13
theorem sound14 : IsCPDerivation F history14 :=
  recode (IsCPDerivation.add (e := line11) (e' := line12) sound13 (earlier history13 2 (by decide)) (earlier history13 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line15 : L := dataLine [0, 0, 0, 0, -2, 0, 0, -2, 0, 0, -2, 0] (-3)
def history15 : List L := line15 :: history14
theorem sound15 : IsCPDerivation F history15 :=
  recode (IsCPDerivation.add (e := line13) (e' := line14) sound14 (earlier history14 1 (by decide)) (earlier history14 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line16 : L := dataLine [0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0] (-1)
def history16 : List L := line16 :: history15
theorem sound16 : IsCPDerivation F history16 :=
  recode (IsCPDerivation.div (e := line15) 2 sound15 (earlier history15 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line17 : L := dataLine [0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] (-1)
def history17 : List L := line17 :: history16
theorem sound17 : IsCPDerivation F history17 :=
  recode (IsCPDerivation.ax (pair 1 0 2) sound16 (pairMem 1 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line18 : L := dataLine [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] (-1)
def history18 : List L := line18 :: history17
theorem sound18 : IsCPDerivation F history18 :=
  recode (IsCPDerivation.ax (pair 1 0 3) sound17 (pairMem 1 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line19 : L := dataLine [0, -2, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0] (-2)
def history19 : List L := line19 :: history18
theorem sound19 : IsCPDerivation F history19 :=
  recode (IsCPDerivation.add (e := line17) (e' := line18) sound18 (earlier history18 1 (by decide)) (earlier history18 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line20 : L := dataLine [0, -2, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0] (-3)
def history20 : List L := line20 :: history19
theorem sound20 : IsCPDerivation F history20 :=
  recode (IsCPDerivation.add (e := line13) (e' := line19) sound19 (earlier history19 6 (by decide)) (earlier history19 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line21 : L := dataLine [0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0] (-1)
def history21 : List L := line21 :: history20
theorem sound21 : IsCPDerivation F history21 :=
  recode (IsCPDerivation.div (e := line20) 2 sound20 (earlier history20 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line22 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0] (-1)
def history22 : List L := line22 :: history21
theorem sound22 : IsCPDerivation F history22 :=
  recode (IsCPDerivation.ax (pair 2 0 2) sound21 (pairMem 2 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line23 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1] (-1)
def history23 : List L := line23 :: history22
theorem sound23 : IsCPDerivation F history23 :=
  recode (IsCPDerivation.ax (pair 2 0 3) sound22 (pairMem 2 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line24 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1] (-1)
def history24 : List L := line24 :: history23
theorem sound24 : IsCPDerivation F history24 :=
  recode (IsCPDerivation.ax (pair 2 2 3) sound23 (pairMem 2 2 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line25 : L := dataLine [0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, -1] (-2)
def history25 : List L := line25 :: history24
theorem sound25 : IsCPDerivation F history25 :=
  recode (IsCPDerivation.add (e := line22) (e' := line23) sound24 (earlier history24 2 (by decide)) (earlier history24 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line26 : L := dataLine [0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, -2] (-3)
def history26 : List L := line26 :: history25
theorem sound26 : IsCPDerivation F history26 :=
  recode (IsCPDerivation.add (e := line24) (e' := line25) sound25 (earlier history25 1 (by decide)) (earlier history25 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line27 : L := dataLine [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1] (-1)
def history27 : List L := line27 :: history26
theorem sound27 : IsCPDerivation F history27 :=
  recode (IsCPDerivation.div (e := line26) 2 sound26 (earlier history26 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line28 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0] (-1)
def history28 : List L := line28 :: history27
theorem sound28 : IsCPDerivation F history28 :=
  recode (IsCPDerivation.ax (pair 2 0 1) sound27 (pairMem 2 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line29 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] (-1)
def history29 : List L := line29 :: history28
theorem sound29 : IsCPDerivation F history29 :=
  recode (IsCPDerivation.ax (pair 2 1 3) sound28 (pairMem 2 1 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line30 : L := dataLine [0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1] (-2)
def history30 : List L := line30 :: history29
theorem sound30 : IsCPDerivation F history30 :=
  recode (IsCPDerivation.add (e := line23) (e' := line28) sound29 (earlier history29 6 (by decide)) (earlier history29 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line31 : L := dataLine [0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -2] (-3)
def history31 : List L := line31 :: history30
theorem sound31 : IsCPDerivation F history31 :=
  recode (IsCPDerivation.add (e := line29) (e' := line30) sound30 (earlier history30 1 (by decide)) (earlier history30 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line32 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1] (-1)
def history32 : List L := line32 :: history31
theorem sound32 : IsCPDerivation F history32 :=
  recode (IsCPDerivation.div (e := line31) 2 sound31 (earlier history31 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line33 : L := dataLine [0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-1)
def history33 : List L := line33 :: history32
theorem sound33 : IsCPDerivation F history33 :=
  recode (IsCPDerivation.ax (pair 2 1 2) sound32 (pairMem 2 1 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line34 : L := dataLine [0, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-2)
def history34 : List L := line34 :: history33
theorem sound34 : IsCPDerivation F history34 :=
  recode (IsCPDerivation.add (e := line22) (e' := line28) sound33 (earlier history33 11 (by decide)) (earlier history33 5 (by decide))) (by decide +kernel) (by decide +kernel)

def line35 : L := dataLine [0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0] (-3)
def history35 : List L := line35 :: history34
theorem sound35 : IsCPDerivation F history35 :=
  recode (IsCPDerivation.add (e := line33) (e' := line34) sound34 (earlier history34 1 (by decide)) (earlier history34 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line36 : L := dataLine [0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0] (-1)
def history36 : List L := line36 :: history35
theorem sound36 : IsCPDerivation F history36 :=
  recode (IsCPDerivation.div (e := line35) 2 sound35 (earlier history35 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line37 : L := dataLine [0, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0, -2] (-2)
def history37 : List L := line37 :: history36
theorem sound37 : IsCPDerivation F history37 :=
  recode (IsCPDerivation.add (e := line27) (e' := line32) sound36 (earlier history36 9 (by decide)) (earlier history36 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line38 : L := dataLine [0, 0, -3, 0, 0, -2, 0, 0, -2, 0, 0, -2] (-3)
def history38 : List L := line38 :: history37
theorem sound38 : IsCPDerivation F history38 :=
  recode (IsCPDerivation.add (e := line36) (e' := line37) sound37 (earlier history37 1 (by decide)) (earlier history37 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line39 : L := dataLine [0, 0, -6, 0, 0, -4, 0, 0, -4, 0, 0, -4] (-6)
def history39 : List L := line39 :: history38
theorem sound39 : IsCPDerivation F history39 :=
  recode (IsCPDerivation.mul (e := line38) 2 sound38 (earlier history38 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line40 : L := dataLine [0, -2, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0] (-2)
def history40 : List L := line40 :: history39
theorem sound40 : IsCPDerivation F history40 :=
  recode (IsCPDerivation.add (e := line4) (e' := line21) sound39 (earlier history39 35 (by decide)) (earlier history39 18 (by decide))) (by decide +kernel) (by decide +kernel)

def line41 : L := dataLine [0, -6, 0, 0, -3, 0, 0, -3, 0, 0, -3, 0] (-6)
def history41 : List L := line41 :: history40
theorem sound41 : IsCPDerivation F history41 :=
  recode (IsCPDerivation.mul (e := line40) 3 sound40 (earlier history40 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line42 : L := dataLine [0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0] (2)
def history42 : List L := line42 :: history41
theorem sound42 : IsCPDerivation F history42 :=
  recode (IsCPDerivation.add (e := line1) (e' := line2) sound41 (earlier history41 40 (by decide)) (earlier history41 39 (by decide))) (by decide +kernel) (by decide +kernel)

def line43 : L := dataLine [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] (3)
def history43 : List L := line43 :: history42
theorem sound43 : IsCPDerivation F history43 :=
  recode (IsCPDerivation.add (e := line3) (e' := line42) sound42 (earlier history42 39 (by decide)) (earlier history42 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line44 : L := dataLine [0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1] (2)
def history44 : List L := line44 :: history43
theorem sound44 : IsCPDerivation F history44 :=
  recode (IsCPDerivation.add (e := line10) (e' := line43) sound43 (earlier history43 33 (by decide)) (earlier history43 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line45 : L := dataLine [0, 0, 0, 0, 4, 4, 0, 4, 4, 0, 4, 4] (8)
def history45 : List L := line45 :: history44
theorem sound45 : IsCPDerivation F history45 :=
  recode (IsCPDerivation.mul (e := line44) 4 sound44 (earlier history44 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line46 : L := dataLine [6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0] (6)
def history46 : List L := line46 :: history45
theorem sound46 : IsCPDerivation F history46 :=
  recode (IsCPDerivation.mul (e := line0) 6 sound45 (earlier history45 45 (by decide))) (by decide +kernel) (by decide +kernel)

def line47 : L := dataLine [0, 0, -6, 0, -1, -4, 0, -1, -4, 0, -1, -4] (-7)
def history47 : List L := line47 :: history46
theorem sound47 : IsCPDerivation F history47 :=
  recode (IsCPDerivation.add (e := line16) (e' := line39) sound46 (earlier history46 30 (by decide)) (earlier history46 7 (by decide))) (by decide +kernel) (by decide +kernel)

def line48 : L := dataLine [0, -6, -6, 0, -4, -4, 0, -4, -4, 0, -4, -4] (-13)
def history48 : List L := line48 :: history47
theorem sound48 : IsCPDerivation F history48 :=
  recode (IsCPDerivation.add (e := line41) (e' := line47) sound47 (earlier history47 6 (by decide)) (earlier history47 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line49 : L := dataLine [0, -6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history49 : List L := line49 :: history48
theorem sound49 : IsCPDerivation F history49 :=
  recode (IsCPDerivation.add (e := line45) (e' := line48) sound48 (earlier history48 3 (by decide)) (earlier history48 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line50 : L := dataLine [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history50 : List L := line50 :: history49
theorem sound50 : IsCPDerivation F history50 :=
  recode (IsCPDerivation.add (e := line46) (e' := line49) sound49 (earlier history49 3 (by decide)) (earlier history49 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line51 : L := dataLine [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history51 : List L := line51 :: history50
theorem sound51 : IsCPDerivation F history51 :=
  recode (IsCPDerivation.div (e := line50) 6 sound50 (earlier history50 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line52 : L := dataLine [-1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] (-1)
def history52 : List L := line52 :: history51
theorem sound52 : IsCPDerivation F history52 :=
  recode (IsCPDerivation.ax (pair 0 0 1) sound51 (pairMem 0 0 1 (by decide))) (by decide +kernel) (by decide +kernel)

def line53 : L := dataLine [-1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] (-1)
def history53 : List L := line53 :: history52
theorem sound53 : IsCPDerivation F history53 :=
  recode (IsCPDerivation.ax (pair 0 0 2) sound52 (pairMem 0 0 2 (by decide))) (by decide +kernel) (by decide +kernel)

def line54 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0] (-1)
def history54 : List L := line54 :: history53
theorem sound54 : IsCPDerivation F history54 :=
  recode (IsCPDerivation.ax (pair 0 0 3) sound53 (pairMem 0 0 3 (by decide))) (by decide +kernel) (by decide +kernel)

def line55 : L := dataLine [0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, -1] (-2)
def history55 : List L := line55 :: history54
theorem sound55 : IsCPDerivation F history55 :=
  recode (IsCPDerivation.add (e := line29) (e' := line33) sound54 (earlier history54 25 (by decide)) (earlier history54 21 (by decide))) (by decide +kernel) (by decide +kernel)

def line56 : L := dataLine [0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, -2] (-3)
def history56 : List L := line56 :: history55
theorem sound56 : IsCPDerivation F history56 :=
  recode (IsCPDerivation.add (e := line24) (e' := line55) sound55 (earlier history55 31 (by decide)) (earlier history55 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line57 : L := dataLine [-1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] (2)
def history57 : List L := line57 :: history56
theorem sound57 : IsCPDerivation F history57 :=
  recode (IsCPDerivation.add (e := line43) (e' := line52) sound56 (earlier history56 13 (by decide)) (earlier history56 4 (by decide))) (by decide +kernel) (by decide +kernel)

def line58 : L := dataLine [-2, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1] (1)
def history58 : List L := line58 :: history57
theorem sound58 : IsCPDerivation F history58 :=
  recode (IsCPDerivation.add (e := line53) (e' := line57) sound57 (earlier history57 4 (by decide)) (earlier history57 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line59 : L := dataLine [-3, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1] (0)
def history59 : List L := line59 :: history58
theorem sound59 : IsCPDerivation F history59 :=
  recode (IsCPDerivation.add (e := line54) (e' := line58) sound58 (earlier history58 4 (by decide)) (earlier history58 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line60 : L := dataLine [-3, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1] (-1)
def history60 : List L := line60 :: history59
theorem sound60 : IsCPDerivation F history60 :=
  recode (IsCPDerivation.add (e := line16) (e' := line59) sound59 (earlier history59 43 (by decide)) (earlier history59 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line61 : L := dataLine [-6, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2] (-2)
def history61 : List L := line61 :: history60
theorem sound61 : IsCPDerivation F history61 :=
  recode (IsCPDerivation.mul (e := line60) 2 sound60 (earlier history60 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line62 : L := dataLine [-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (-5)
def history62 : List L := line62 :: history61
theorem sound62 : IsCPDerivation F history62 :=
  recode (IsCPDerivation.add (e := line56) (e' := line61) sound61 (earlier history61 5 (by decide)) (earlier history61 0 (by decide))) (by decide +kernel) (by decide +kernel)

def line63 : L := dataLine [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (0)
def history63 : List L := line63 :: history62
theorem sound63 : IsCPDerivation F history63 :=
  recode (IsCPDerivation.div (e := line62) 6 sound62 (earlier history62 0 (by decide)) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def line64 : L := dataLine [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (1)
def history64 : List L := line64 :: history63
theorem sound64 : IsCPDerivation F history64 :=
  recode (IsCPDerivation.add (e := line51) (e' := line63) sound63 (earlier history63 12 (by decide)) (earlier history63 0 (by decide))) (by decide +kernel) (by decide +kernel)

theorem certificate : ∃ π : List L, IsCPRefutation F π ∧ π.length = 65 := by
  have eq : line64 = ((0 : V → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) rfl
  refine ⟨history64, ⟨sound64, ?_⟩, rfl⟩
  rw [← eq]
  exact earlier history64 0 (by decide)

end PHPInterval65

#print axioms PHPInterval65.certificate
