"""Independent exact-state audit for the K4 capacity and residual CP counts."""
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import gcd

ZERO = (0,) * 5
TARGET = (0,0,0,0,1)
CAPACITY = (-1,)*5
EDGES = [tuple(-int(i in e) for i in range(4)) + (-1,) for e in combinations(range(4),2)]
RESIDUAL = EDGES + [(1,1,1,1,2)]

def plus(x,y):
    return tuple(a+b for a,b in zip(x,y))

def cuts(x):
    g = gcd(*x[:4])
    if g == 0:
        # On the states visited here, all other zero-vector cuts would either
        # preserve an already-available contradiction, or weaken the line.
        if x[-1] != 0: raise ValueError(f'unexpected constant {x}')
    for d in range(2, g+1):
        if g % d == 0:
            yield tuple(a//d for a in x[:4])+(-((-x[-1])//d),)

def exact(lines):
    @cache
    def trees(mask, ncuts, ndoubles):
        out = set()
        if mask.bit_count()==1 and ncuts==ndoubles==0:
            out.add(lines[mask.bit_length()-1])
        p = (mask-1) & mask
        while p:
            q = mask ^ p
            if p<q:
                for n in range(ncuts+1):
                    for d in range(ndoubles+1):
                        for left,right in product(trees(p,n,d), trees(q,ncuts-n,ndoubles-d)):
                            out.add(plus(left,right))
            p = (p-1) & mask
        if ncuts:
            for parent in trees(mask,ncuts-1,ndoubles):
                out.update(cuts(parent))
        if ndoubles:
            for line in trees(mask,ncuts,ndoubles-1):
                out.add(plus(line,line))
        return out
    return trees

def arbitrary_multipliers():
    """Solve all five exact equations for k simultaneously, with exact rational arithmetic."""
    counts = {}
    for assignment in product(range(3),repeat=7):
        a,b,c = (tuple(sum(line[i] for j,line in enumerate(RESIDUAL) if assignment[j]==v)
                         for i in range(5)) for v in range(3))
        for x in cuts(a):
            inner = plus(x,b)
            outer = tuple(t-z for t,z in zip(TARGET,c))
            if any(i==0 and j!=0 for i,j in zip(inner,outer)):
                continue
            ratios={Fraction(j,i) for i,j in zip(inner,outer) if i}
            if not ratios: raise ValueError('all nonnegative k would work')
            if len(ratios)==1:
                k=ratios.pop()
                if k>=0 and k.denominator==1:
                    counts[int(k)] = counts.get(int(k),0)+1
    return counts

if __name__=='__main__':
    col = exact(EDGES)
    for n in range(3):
        states = col(63,n,0)
        assert CAPACITY not in states
        print('column read-once cuts', n,'states',len(states))
    assert CAPACITY in col(63,2,1)
    residual = exact(RESIDUAL)
    for n,d in [(0,0),(1,0),(2,0),(0,1),(1,1)]:
        states=residual(127,n,d)
        assert TARGET not in states
        print('residual cuts / doubles', n,d,'states',len(states))
    choices = arbitrary_multipliers()
    print('unrestricted nonnegative integer k solving k*(cut(A)+B)+C = (0,1):',choices)
    assert not choices
