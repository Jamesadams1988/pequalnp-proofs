"""Check chronological BPHP(5,2) steps and emit one self-contained Lean file.

A step is one of the following JSON objects:
  {"rule":"ax", "p":0, "q":1, "hole":0}
  {"rule":"res", "neg":0, "pos":1, "pivot":1}
  {"rule":"weak", "parent":0, "clause":[[1,true],[2,true],[5,true]]}
Parent indices start at zero. Bit 2*p+b denotes bit b of pigeon p. A mask
is one linear form, and the Boolean paired with it is its right-hand side.
The generator computes the axiom and resolvent clauses. Semantic weakening
requires an explicit child clause. Finish by passing the emitted file to Lean.
"""
import argparse
import functools
import json
import pathlib


@functools.cache
def eq_table(mask, rhs):
    return sum(1 << x for x in range(1024) if (mask & x).bit_count() % 2 == rhs)


def truth_table(clause):
    table = 0
    for mask, rhs in clause:
        table |= eq_table(mask, rhs)
    return table


def natural(v, limit):
    if type(v) is not int or not 0 <= v < limit:
        raise ValueError(f'expected integer in [0,{limit}), got {v!r}')
    return v


def boolean(v):
    if type(v) not in (int, bool) or v not in (0, 1):
        raise ValueError(f'invalid Boolean {v!r}')
    return bool(v)


def axiom(p, q, hole):
    return frozenset((1 << (2*k + b), not bool(hole & (1 << b)))
                     for k in (p, q) for b in range(2))


def variables(mask):
    return [f'({i//2},{i%2})' for i in range(10) if mask & (1 << i)]


def form(mask):
    entries = variables(mask)
    return '({' + ','.join(entries) + '} : Finset V)' if entries else '(∅ : Finset V)'


def as_lean(clause):
    eqlist = [f'({form(m)},{str(v).lower()})' for m,v in sorted(clause)]
    return '{' + ','.join(eqlist) + '}' if eqlist else '∅'


def get_parent(step, key, index):
    return natural(step[key], index)


def emit(steps, budget, prefix=False):
    lines = []
    text = []
    needs_semantic = False
    def parent_mem(i, j):
        return f'(lineAt p{i-1} {i-1-j} (by decide +kernel))'
    for i,step in enumerate(steps):
        try:
            rule = step['rule']
            previous = f'd{i-1}' if i else 'IsLinDerivation.nil'
            if rule == 'ax':
                p,q,h = natural(step['p'],5),natural(step['q'],5),natural(step['hole'],4)
                if p == q:
                    raise ValueError('a collision axiom needs distinct pigeons')
                clause = axiom(p,q,h)
                value = f'linOfClause (inputClause {p} {q} {h})'
                reason = f'IsLinDerivation.ax {previous} (inputMem {p} {q} {h} (by decide))'
            elif rule == 'res':
                j,k = get_parent(step,'neg',i),get_parent(step,'pos',i)
                mask = natural(step['pivot'],1024)
                if (mask,False) not in lines[j] or (mask,True) not in lines[k]:
                    raise ValueError('pivot sign absent from designated parent')
                clause = (lines[j] - {(mask,False)}) | (lines[k] - {(mask,True)})
                value = as_lean(clause)
                reason = (f'IsLinDerivation.res (C := l{j}) (D := l{k}) {previous}\n'
                          f'    {parent_mem(i,j)} {parent_mem(i,k)}\n'
                          f'    ⟨{form(mask)}, by decide +kernel, by decide +kernel, by decide +kernel⟩')
            elif rule == 'weak':
                j = get_parent(step,'parent',i)
                clause = frozenset((natural(m,1024),boolean(v)) for m,v in step['clause'])
                if truth_table(lines[j]) & ~truth_table(clause):
                    raise ValueError('invalid semantic implication')
                value = as_lean(clause)
                if lines[j] <= clause:
                    inference = (f'(by intro a h; obtain ⟨q,hq,hs⟩ := h; '\
                                 f'exact ⟨q,(by decide +kernel : l{j} ⊆ l{i}) hq,hs⟩)')
                else:
                    needs_semantic = True
                    mask = 0
                    for z,_ in lines[j] | clause:
                        mask |= z
                    support = '['+','.join(variables(mask))+']'
                    inference = (f'(checkedWeak {support} l{j} l{i}\n'
                                 '      (by decide +kernel) (by decide +kernel) (by decide +kernel))')
                reason = (f'IsLinDerivation.weak (C := l{j}) {previous}\n'
                          f'    {parent_mem(i,j)} {inference}')
            else:
                raise ValueError(f'unknown rule {rule!r}')
        except (KeyError,TypeError,ValueError) as exc:
            raise ValueError(f'line {i}: {exc}') from exc
        lines.append(clause)
        tail = f'p{i-1}' if i else '[]'
        text.append(f'private def l{i} : LC := {value}\nprivate def p{i} : List LC := l{i} :: {tail}\n'
                    f'private theorem d{i} : IsLinDerivation F p{i} :=\n  {reason}\n')
    if not lines:
        raise ValueError('empty trace')
    i = len(lines)-1
    header = pathlib.Path(__file__).with_name('Template.lean').read_text().split('\nend PEqualNP.Outside.L_pcx_133')[0]
    if not needs_semantic:
        header = header.split('-- SEMANTIC WEAKENING')[0]
    else:
        header = header.replace('-- SEMANTIC WEAKENING\n','').replace('-- END SEMANTIC WEAKENING\n','')
    if prefix:
        end = f'private theorem validatedPrefix : IsLinDerivation F p{i} := d{i}\n'
    else:
        if len(lines)>budget or lines[-1]:
            raise ValueError(f'expected empty final line at budget {budget}, got {len(lines)} lines and {lines[-1]}')
        end = ('theorem _root_.PEqualNP.Outside.L_pcx_133 :\n'
               '    ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)),\n'
               '      PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧\n'
               f'      π.length ≤ {budget} :=\n  ⟨p{i},⟨d{i},List.Mem.head _⟩,by decide +kernel⟩\n')
    source = '\n'.join([header,*text,end,'end PEqualNP.Outside.L_pcx_133\n'])
    if not prefix and budget != 127:
        source = source.replace('_root_.PEqualNP.Outside.L_pcx_133', f'_root_.Row133.refutation{budget}')
        source = source.replace('PEqualNP.Outside.L_pcx_133', f'Row133.Budget{budget}')
    return source


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('steps',type=pathlib.Path)
    parser.add_argument('output',type=pathlib.Path)
    parser.add_argument('--budget',type=int,default=127)
    parser.add_argument('--prefix',action='store_true',help='verify a partial derivation without claiming a refutation')
    args = parser.parse_args()
    args.output.write_text(emit(json.loads(args.steps.read_text()),args.budget,args.prefix))
