"""Validate chronological unary PHP(5,4) resolution and emit a single Lean file.

JSON steps are {"rule":"pigeon","p":0}, {"rule":"hole","p":0,"q":1,"h":0},
or {"rule":"res","pos":0,"neg":1,"pivot":0}. Line numbers are zero-based.
The pivot is a variable index 4*pigeon + hole. Each resolvent is calculated
from its parents. The trace must end with the empty clause.
"""
import argparse
import json
from pathlib import Path


def bounded(value, limit):
    if type(value) is not int or not 0 <= value < limit:
        raise ValueError(f'expected integer below {limit}, got {value!r}')
    return value


def pigeon(p):
    return frozenset((4*p+h, True) for h in range(4))


def hole(p, q, h):
    return frozenset(((4*p+h, False), (4*q+h, False)))


def clause_lean(c):
    if not c:
        return '∅'
    items = [f'(({v//4},{v%4}),{str(s).lower()})' for v,s in sorted(c)]
    return '{'+','.join(items)+'}'


def validate(steps):
    clauses = []
    constructors = []
    for i,s in enumerate(steps):
        try:
            rule = s['rule']
            if rule == 'pigeon':
                p = bounded(s['p'],5)
                clause = pigeon(p)
                node = f'.pigeon {p}'
            elif rule == 'hole':
                p,q,h = bounded(s['p'],5),bounded(s['q'],5),bounded(s['h'],4)
                if p == q:
                    raise ValueError('collision clause requires distinct pigeons')
                clause = hole(p,q,h)
                node = f'.hole {p} {q} {h}'
            elif rule == 'res':
                pos,neg = bounded(s['pos'],i),bounded(s['neg'],i)
                v = bounded(s['pivot'],20)
                if (v,True) not in clauses[pos] or (v,False) not in clauses[neg]:
                    raise ValueError('pivot is absent with its designated sign')
                clause = (clauses[pos] - {(v,True)}) | (clauses[neg] - {(v,False)})
                node = f'.resolve {i-1-pos} {i-1-neg} ({v//4},{v%4}) {clause_lean(clause)}'
            else:
                raise ValueError(f'unknown inference {rule!r}')
        except (KeyError,TypeError,ValueError) as e:
            raise ValueError(f'line {i}: {e}') from e
        clauses.append(clause)
        constructors.append(node)
    if not clauses or clauses[-1]:
        raise ValueError('final clause is not empty')
    return clauses, constructors


def tree_proof(steps, clauses, budget):
    uses = [0] * len(steps)
    leaves = []
    proof = ["section Tree", "variable (P : Cl → ℕ → Prop)",
             "variable (leaf : ∀ C ∈ PHP 5 4, P C 1)",
             "variable (fork : ∀ {A B R : Cl} {l r : ℕ}, P A l → P B r → IsResolvent A B R → P R (l+r))", ""]
    for i, (step, clause) in enumerate(zip(steps,clauses)):
        rule = step['rule']
        if rule == 'res':
            a,b,v = step['pos'], step['neg'], step['pivot']
            uses[a] += 1
            uses[b] += 1
            leaves.append(leaves[a] + leaves[b])
            def premise(j):
                args = 'P leaf fork' if steps[j]['rule']=='res' else 'P leaf'
                return f'(tree{j} {args})'
            body = (f'fork {premise(a)} {premise(b)} '
                    f'⟨({v//4},{v%4}),by decide +kernel,by decide +kernel,by decide +kernel⟩')
            value = clause_lean(clause)
        elif rule == 'pigeon':
            p = step['p']
            value = f'(Step.pigeon {p}).line'
            body = f'leaf _ (.inl ⟨{p},rfl⟩)'
            leaves.append(1)
        else:
            p,q,h = step['p'],step['q'],step['h']
            value = f'(Step.hole {p} {q} {h}).line'
            body = f'leaf _ (.inr ⟨{p},{q},{h},by decide,rfl⟩)'
            leaves.append(1)
        include = 'include leaf fork in' if rule == 'res' else 'include leaf in'
        proof.extend([f'private def c{i} : Cl := {value}', include, f'private theorem tree{i} : P c{i} {leaves[i]} := {body}', ''])
    if uses != [1]*(len(steps)-1)+[0]:
        raise ValueError('tree mode requires every non-root line to be used exactly once')
    proof.extend([f'/-- Recursion principle witness for an ordinary resolution tree with exactly {leaves[-1]} axiom leaves. -/',
                  f'theorem _root_.Row169.tree{budget} (P : Clause (Fin 5 × Fin 4) → ℕ → Prop)',
                  '    (leaf : ∀ C ∈ PHP 5 4, P C 1)',
                  '    (fork : ∀ {A B R} {l r : ℕ}, P A l → P B r → IsResolvent A B R → P R (l+r)) :',
                  f'    P ∅ {leaves[-1]} := tree{len(steps)-1} P leaf fork', 'end Tree'])
    return '\n'.join(proof)


def emit(steps,budget,tree=False):
    clauses,nodes = validate(steps)
    if len(steps) > budget:
        raise ValueError(f'{len(steps)} lines exceed the budget {budget}')
    official = budget == 149
    namespace = 'PEqualNP.Outside.L_pcx_169' if official else f'Row169.Budget{budget}'
    theorem = '_root_.PEqualNP.Outside.L_pcx_169' if official else f'_root_.Row169.refutation{budget}'
    template = Path(__file__).with_name('Template.lean').read_text()
    header = template.split('\nend Row169.Certificate')[0].replace('Row169.Certificate',namespace)
    data = 'private def steps : List Step := [\n  '+',\n  '.join(nodes)+']\n'
    proof = f'''private theorem checks : verify steps [] = true := by decide +kernel

private def proofLines : List Cl := (steps.map Step.line).reverse

private theorem derives : IsDerivation (PHP 5 4) proofLines := by
  simpa [proofLines] using verifySound steps [] .nil checks

theorem {theorem} :
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)),
      PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ {budget} :=
  ⟨proofLines,⟨derives,by decide +kernel⟩,by decide +kernel⟩

end {namespace}
'''
    if tree:
        proof = proof.replace(f'end {namespace}', tree_proof(steps,clauses,budget) + f'\n\nend {namespace}')
    return '\n'.join([header,data,proof])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('steps',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--budget',type=int,default=149)
    parser.add_argument('--tree',action='store_true',help='prove the leaf count and reject shared derivations')
    args = parser.parse_args()
    args.output.write_text(emit(json.loads(args.steps.read_text()),args.budget,args.tree))
