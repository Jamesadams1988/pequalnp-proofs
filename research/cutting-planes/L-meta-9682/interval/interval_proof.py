"""Produce and replay exact rank-two proofs for two canonical six-triangle configurations."""
from collections import defaultdict
from functools import cache,reduce
from itertools import combinations
from fractions import Fraction
from math import lcm
from pathlib import Path
import json

pairs=list(combinations(range(4),2))
def build(config):
    code=[]
    @cache
    def emit(op):
        n=len(code);code.append(list(op));return n
    def add(a,b):return emit(('add',min(a,b),max(a,b)))
    @cache
    def row(k):
        if k<4:return emit(('pigeon',k))
        if k<22:
            h,j=divmod(k-4,6)
            return emit(('pair',h,*pairs[j]))
        h,p=divmod(k-22,4)
        es=[row(4+6*h+j) for j,pair in enumerate(pairs) if p not in pair]
        return emit(('div',reduce(add,es),2))
    def agg(k):
        d=lcm(*[Fraction(w).denominator for w in k['rows'].values()])
        groups=defaultdict(list)
        for t,val in k['rows'].items():groups[int(Fraction(val)*d)].append(row(int(t)))
        def scaled(k,x): return x if k==1 else emit(('mul',x,k))
        terms=[scaled(weight,reduce(add,group)) for weight,group in sorted(groups.items())]
        return emit(('div',reduce(add,terms),d))
    add(agg(config['min']),agg(config['max']))
    return code

def verify(code):
    vals=[]
    for op,*args in code:
        coeff=[0]*12
        if op=='pair':
            h,i,j=args;coeff[3*i+h]=coeff[3*j+h]=-1;val=-1;rank=0
        elif op=='pigeon':
            (i,)=args;coeff[3*i:3*i+3]=[1]*3;val=1;rank=0
        elif op=='add':
            i,j=args;a,v,r=vals[i];b,w,s=vals[j];coeff=[x+y for x,y in zip(a,b)];val=v+w;rank=max(r,s)
        elif op=='mul':
            i,k=args;assert k>=0;a,v,rank=vals[i];coeff=[x*k for x in a];val=v*k
        else:
            assert op=='div'
            i,k=args;a,v,rank=vals[i];assert k>0 and all(x%k==0 for x in a);coeff=[x//k for x in a];val=-((-v)//k);rank+=1
        vals.append((coeff,val,rank))
    assert vals[-1]==([0]*12,1,2)

if __name__ == '__main__':
    certificates = Path(__file__).with_name('fractional-branch.json')
    for index, config in enumerate(json.loads(certificates.read_text())):
        program = build(config)
        verify(program)
        print(f'Configuration {index}: {len(program)} lines, two division rounds')
