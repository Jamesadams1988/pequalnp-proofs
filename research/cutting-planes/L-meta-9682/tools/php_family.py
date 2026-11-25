"""Build and verify chronological refutations of PHP(n+1,n) under the project's CP rules."""
from functools import reduce
from itertools import combinations
import json


def proof(n):
    """Return chronological legal operator arrays for n >= 2."""
    if n < 2:
        raise ValueError("at least two holes")
    steps=[]
    def emit(*op):
        steps.append(list(op))
        return len(steps)-1
    def add(i,j): return emit('add',i,j)
    caps=[]
    for h in range(n):
        capped=emit('pair',h,0,1)
        for i in range(2,n+1):
            active=capped if i==2 else emit('mul',capped,i-1)
            for j in range(i):
                active=add(active,emit('pair',h,j,i))
            capped=emit('div',active,i)
        caps.append(capped)
    rows=[emit('pigeon',i) for i in range(n+1)]
    reduce(add,caps+rows)
    return steps


def verify(n,steps):
    seen=[]
    for k,*args in steps:
        if k in ('pair','pigeon'):
            c=[0]*((n+1)*n)
            if k=='pair':
                h,i,j=args
                assert i!=j and 0<=h<n and 0<=i<n+1 and 0<=j<n+1
                c[i*n+h]=c[j*n+h]=-1
                rhs=-1
            else:
                (i,)=args
                assert 0<=i<n+1
                for h in range(n): c[i*n+h]=1
                rhs=1
        elif k=='add':
            a,b=(seen[i] for i in args)
            c=[x+y for x,y in zip(a[0],b[0])]
            rhs=a[1]+b[1]
        elif k=='mul':
            i,t=args;c=[a*t for a in seen[i][0]];rhs=seen[i][1]*t;assert t>=0
        elif k=='div':
            i,t=args;a,b=seen[i];assert t>0 and all(x%t==0 for x in a)
            c=[x//t for x in a];rhs=-((-b)//t)
        else: raise ValueError(k)
        seen.append((c,rhs))
    assert all(x==0 for x in seen[-1][0]) and seen[-1][1]==1
    assert len(seen)==n**3+3*n*n-n+1


if __name__=='__main__':
    lengths={}
    for n in range(2,11):
        s=proof(n);verify(n,s);lengths[n]=len(s)
    print(json.dumps(dict(rule='n^3+3*n^2-n+1', holes_to_lines=lengths), indent=2))
