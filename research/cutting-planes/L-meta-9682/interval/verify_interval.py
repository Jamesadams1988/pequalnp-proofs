"""Exact, standard-library replay of the PHP(4,3) endpoint and dual certificates."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
import json

base=Path(__file__).parent
unit=[[int(k==v) for v in range(12)] for k in range(12)]
def combine(terms):
    return tuple(sum(w*row[j] for w,row in terms) for j in range(12))
def positive(indices):return combine([(1,unit[j]) for j in indices])
rows=[tuple(-x for x in positive(range(3*i,3*i+3))) for i in range(4)]
pairs=[positive([3*i+h,3*k+h]) for h in range(3) for i,k in combinations(range(4),2)]
tris=[positive([3*k+h for k in range(4) if k!=i]) for h in range(3) for i in range(4)]
normals=rows+pairs+tris
rhs=[-1]*4+[1]*30
# These permutations fix x_(0,0); all bounds, rows and column pairs are invariant.
group=[((0,)+i,(0,)+h) for i,h in product(permutations(range(1,4)),permutations(range(1,3)))]
def representative(t):
    return min(tuple(sorted(4*holes[k//4]+pigeons[k%4] for k in t)) for pigeons,holes in group)
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def verify():
    negatives=json.loads((base/'fractional-branch-endpoints.json').read_text())
    cases=set(representative(t) for t in combinations(range(12),5))
    assert set(negatives)=={','.join(map(str,t)) for t in cases}
    for t in cases:
        x=list(map(F,negatives[','.join(map(str,t))]))
        assert len(x)==12 and all(0<=v<=1 for v in x) and x[0] in (0,1)
        assert all(dot(normals[k],x)<=rhs[k] for k in list(range(22))+[22+i for i in t])
    positives=json.loads((base/'fractional-branch.json').read_text())
    for item in positives:
        used=set(item['triangles']); assert len(used)==6
        for name,sign in [('min',-1),('max',1)]:
            cert=item[name]
            assert not cert['lo'] and not cert['hi']
            mult={int(i):F(w) for i,w in cert['rows'].items()}
            assert all(w>0 and 0<=i<34 and (i<22 or i-22 in used) for i,w in mult.items())
            assert combine([(w,normals[i]) for i,w in mult.items()])==tuple(sign*v for v in unit[0])
            bound=sum(w*rhs[i] for i,w in mult.items())
            assert bound==F(cert['upper_rhs'])
            assert (bound<0 if name=='min' else bound<1)
    print(f'All 792 five-triangle sets verified using {len(cases)} exact endpoint witnesses.')
    print(f'{len(positives)} strict interval certificates verified with rational multipliers.')

if __name__=='__main__':verify()
