"""Independently verify the positive SAT model and distinguish both AND-gate conditions."""
import argparse
import subprocess
from itertools import combinations
from pathlib import Path

from verify_small import lower_instance

def evaluate(n, gates, out, row):
    w = [bool(row>>u & 1) for u in range(2*n)]
    for op, parents in gates:
        assert len(parents)<=2 and all(0<=u<len(w) for u in parents)
        vals = [w[u] for u in parents]
        w.append(all(vals) if op=='and' else any(vals))
    return w, w[out] if out<len(w) else False


def properties(n, edges, gates, out):
    exact=guard=onehot=True
    for row in range(1 << (2*n)):
        target=any(row>>a & row>>b & 1 for a,b in edges)
        vals,y=evaluate(n,gates,out,row)
        exact &= y==target
        p,_=evaluate(n,gates,out,row & ((1<<n)-1))
        l,_=evaluate(n,gates,out,row & ~((1<<n)-1))
        for i,(op,_) in enumerate(gates,2*n):
            if op=='and' and vals[i]:
                guard &= p[i] or l[i] or target
                onehot &= row.bit_count()!=1
    return exact,guard,onehot

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('solver', help='path or command name for CaDiCaL')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Python assertions are required; remove -O or PYTHONOPTIMIZE')
    root = args.output / 'controls'
    root.mkdir(parents=True, exist_ok=True)
    edges = [(0,4),(0,5),(1,3),(1,5),(2,3),(2,4)]
    instance = root / 'positive-control.cnf'
    lower_instance(edges, 8).write(instance)
    proc = subprocess.run([args.solver, '--quiet', str(instance)], capture_output=True, text=True)
    if proc.returncode != 10:
        raise SystemExit(f'{instance}: expected SAT (exit 10), got {proc.returncode} {proc.stderr}')
    (root / 'positive-control.log').write_text(proc.stdout)
    # Parse all emitted clauses, independently verify the satisfying assignment.
    rows=(root/'positive-control.log').read_text().splitlines()
    assert 's SATISFIABLE' in rows
    model={int(x) for row in rows if row.startswith('v ') for x in row.split()[1:] if x!='0'}
    cnf=(root/'positive-control.cnf').read_text().splitlines()
    _,_,v,c=cnf[0].split()
    assert len(model)==int(v) and all(-l not in model for l in model)
    assert len(cnf)-1==int(c)
    for row in cnf[1:]:
        clause=list(map(int,row.split()))
        assert clause[-1]==0 and any(l in model for l in clause[:-1])
    # Reconstruct the selected gates, independently check all 64 assignment outputs.
    pos=[1<<a|1<<b for a,b in edges]
    neg=[row for row in range(64) if not any(row&p==p for p in pos)]
    maximal=[row for row in neg if all(row==other or row&other!=row for other in neg)]
    selection_var=(6+8)*(len(pos)+len(maximal))+1
    gates=[]
    for u in range(6,6+8):
        selected=[]
        for a,b in combinations(range(u),2):
            for op in ('or','and'):
                if selection_var in model:
                    selected.append((op,[a,b]))
                selection_var+=1
        assert len(selected)==1
        gates+=selected
    assert properties(3,edges,gates,13)[0]
    print('Positive control: size-eight SAT solution for the six-cycle, all CNF clauses and all 64 rows passed.')
    target=[(0,2)]
    # The second AND in this example produces p1*l1 on a non-edge.
    # The following gates mask that bad signal, leaving the output exactly correct.
    bad_mixed=[('and',[0,2]),('and',[1,3]),('and',[4,5]),('or',[4,6])]
    assert properties(2,target,bad_mixed,7)==(True,False,True)
    # An empty AND is true even on a one-hot row. Here it feeds the final gate.
    bad_onehot=[('and',[0,2]),('and',[]),('and',[4,5])]
    assert properties(2,target,bad_onehot,6)==(True,True,False)
    assert properties(0,[],[],0)==(True,True,True)
    print('Negative controls: mixed non-edge AND and empty AND violate their respective conditions. Missing output computes false.')

if __name__=='__main__':
    main()
