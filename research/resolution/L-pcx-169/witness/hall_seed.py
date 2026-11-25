import itertools
import json
from pathlib import Path


def make():
    steps, clauses, found = [], [], {}
    def emit(clause, step):
        clause = frozenset(clause)
        if clause not in found:
            found[clause] = len(steps)
            steps.append(step)
            clauses.append(clause)
        return found[clause]
    def res(n, p, var):
        assert -var in clauses[n] and var in clauses[p]
        return emit((clauses[n] - {-var}) | (clauses[p] - {var}), dict(rule="res", neg=n, pos=p, pivot=var-1))
    def x(p, h):
        return 4*p+h+1
    pigeons = [emit([x(i,h) for h in range(4)], dict(rule="pigeon", p=i)) for i in range(5)]
    holes = {(i,j,h):emit([-x(i,h),-x(j,h)],dict(rule="hole",p=i,q=j,h=h)) for j in range(5) for i in range(j) for h in range(4)}
    hall = {():pigeons[0]}
    for k in range(1,5):
        new = {}
        for S in itertools.combinations(range(4),k):
            last = pigeons[k]
            for h in S:
                cond = hall[tuple(t for t in S if t != h)]
                for i in range(k):
                    cond = res(holes[i,k,h],cond,x(i,h))
                last = res(cond,last,x(k,h))
            new[S]=last
        hall=new
    assert not clauses[-1] and len(steps)==157
    return steps, clauses


if __name__ == '__main__':
    steps, clauses=make()
    Path('hall157.json').write_text(json.dumps(steps)+'\n')
    with open('hall157.dat','w') as f:
        for s,c in zip(steps,clauses):
            m=sum(1<<(abs(l)-1+(20 if l<0 else 0)) for l in c)
            print(m, s.get('neg',-1),s.get('pos',-1),s.get('pivot',-1),file=f)
