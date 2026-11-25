"""Encode and validate an explicit cutting-planes refutation of PHP(4,3).

Read chronological JSON instructions from a file, or use the usual 52-line
capacity proof by default. Write a standalone Lean source to stdout. Line
indices start at zero. Input steps are ["pigeon", i], ["pair", h, i, j],
["lo", i, h], ["hi", i, h], ["add", a, b], ["mul", a, k], or ["div", a, d].
With --refute-assigned, generate the exact negation of L-meta-9682. That mode
requires a refutation of at most 51 lines.
"""
import argparse
import json
from pathlib import Path

N = 12
HEADER = """import PEqualNP.Defs

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
"""

def control():
    steps = []
    def step(*args):
        steps.append(list(args))
        return len(steps)-1
    def sum_lines(*xs):
        result = xs[0]
        for x in xs[1:]:
            result = step('add', result, x)
        return result
    caps = []
    for h in range(3):
        xy, xz, yz = (step('pair', h, i, j) for i, j in ((0,1),(0,2),(1,2)))
        tri = step('div', sum_lines(xy, xz, yz), 2)
        spokes = [step('pair', h, i, 3) for i in range(3)]
        weighted = step('mul', tri, 2)
        caps.append(step('div', sum_lines(*spokes, weighted), 3))
    birds = [step('pigeon', p) for p in range(4)]
    sum_lines(*caps, *birds)
    return steps


def point(p, h):
    if not (0 <= p < 4 and 0 <= h < 3):
        raise ValueError(f'invalid PHP variable {(p,h)}')
    return 3*p+h


def compile_certificate(steps, assigned):
    results = []
    output = [HEADER]
    for number, instruction in enumerate(steps):
        prev = f'history{number-1}' if number else 'empty'
        ok = f'sound{number-1}' if number else 'start'
        def member(a):
            if not 0 <= a < number:
                raise ValueError(f'unknown previous line {a} at {number}')
            return f'(earlier {prev} {number-1-a} (by decide))'
        coeffs = [0]*N
        if not isinstance(instruction,list) or not instruction or not all(type(n) is int for n in instruction[1:]):
            raise ValueError(f'invalid instruction at line {number}: {instruction!r}')
        match instruction:
            case ['pigeon', p]:
                for h in range(3): coeffs[point(p,h)] = 1
                rhs = 1
                proof = f'IsCPDerivation.ax (pigeon {p}) {ok} (pigeonMem {p})'
            case ['pair', h, p, q] if p != q:
                coeffs[point(p,h)] = coeffs[point(q,h)] = -1
                rhs = -1
                proof = f'IsCPDerivation.ax (pair {h} {p} {q}) {ok} (pairMem {h} {p} {q} (by decide))'
            case [tag, p, h] if tag in ('lo','hi'):
                coeffs[point(p,h)] = 1 if tag=='lo' else -1
                rhs = 0 if tag=='lo' else -1
                ctor = 'boolLo' if tag=='lo' else 'boolHi'
                proof = f'IsCPDerivation.{ctor} (({p}, {h}) : V) {ok}'
            case ['add', a, b]:
                ma, mb = member(a), member(b)
                ca, va = results[a]; cb, vb = results[b]
                coeffs = [x+y for x,y in zip(ca,cb)]
                rhs = va+vb
                proof = f'IsCPDerivation.add (e := line{a}) (e\' := line{b}) {ok} {ma} {mb}'
            case ['mul', a, k] if k >= 0:
                m = member(a)
                c,v = results[a]
                coeffs = [k*x for x in c]
                rhs = k*v
                proof = f'IsCPDerivation.mul (e := line{a}) {k} {ok} {m}'
            case ['div', a, d] if d > 0:
                m = member(a)
                c,v = results[a]
                if any(x%d for x in c): raise ValueError(f'nonintegral coefficients at line {number}')
                coeffs = [x//d for x in c]
                rhs = -((-v)//d)
                proof = f'IsCPDerivation.div (e := line{a}) {d} {ok} {m} (by decide) (by decide +kernel)'
            case _:
                raise ValueError(f'invalid instruction at line {number}: {instruction!r}')
        results.append((coeffs,rhs))
        output.append(f'def line{number} : L := dataLine {coeffs} ({rhs})\n'
                      f'def history{number} : List L := line{number} :: {prev}\n'
                      f'theorem sound{number} : IsCPDerivation F history{number} :=\n'
                      f'  recode ({proof}) (by decide +kernel) (by decide +kernel)\n')
    last = len(steps) - 1
    if ([0]*N,1) not in results:
        raise ValueError('certificate must contain 0 ≥ 1')
    final = results.index(([0]*N,1))
    output.append(f'''theorem certificate : ∃ π : List L, IsCPRefutation F π ∧ π.length = {len(steps)} := by
  have eq : line{final} = ((0 : V → ℤ), (1 : ℤ)) := Prod.ext (funext (by decide +kernel)) rfl
  refine ⟨history{last}, ⟨sound{last}, ?_⟩, rfl⟩
  rw [← eq]
  exact earlier history{last} {last-final} (by decide)

end PEqualNP.Outside.L_meta_9682.Certificate''')
    if assigned:
        if len(steps) > 51: raise ValueError('L-meta-9682 requires at most 51 lines')
        output.append('''theorem PEqualNP.Outside.L_meta_9682 :
    ¬ (¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (3 + 1) × Fin 3)),
      PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (3 + 1) 3) π ∧
      π.length ≤ 51)) := by
  intro h
  obtain ⟨π, hp, hl⟩ := PEqualNP.Outside.L_meta_9682.Certificate.certificate
  exact h ⟨π, hp, by omega⟩''')
    return '\n'.join(output) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('program', type=Path, nargs='?')
    parser.add_argument('--refute-assigned', action='store_true')
    args = parser.parse_args()
    program = json.loads(args.program.read_text()) if args.program else control()
    print(compile_certificate(program, args.refute_assigned), end='')
