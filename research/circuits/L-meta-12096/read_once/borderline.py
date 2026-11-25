"""List surviving top rectangles for a concrete correlated six-wire bank."""
from functools import cache
from itertools import combinations
import json
F=0xfe80fe00fe00e800; universe=(1<<64)-1
wires=(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffff00ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)

def split(active):
    for n in range(1,len(active)//2+1):
        for a in combinations(active,n):
            b=tuple(i for i in active if i not in a)
            if len(a)!=len(b) or a<b: yield a,b

@cache
def tables(side):
    if len(side)==1:
        x=wires[side[0]];return frozenset((x,x^universe))
    output=set()
    for a,b in split(side):
        for u in tables(a):
            for v in tables(b):output.update((u&v, (u&v)^universe))
    return frozenset(output)

def closure(side,yes):
    buckets={}
    for r in range(64):
        sig=tuple((wires[i]>>r)&1 for i in side)
        buckets[sig]=buckets.get(sig,0)|(1<<r)
    return sum(x for x in buckets.values() if x&yes)

summary=[]
def reject(active,yes,no,depth):
    if len(active)==1:return not any(yes&~t==0 and no&t==0 for t in tables(active))
    if no&closure(active,yes):return True
    for a,b in split(active):
        for polarity,(y,z) in enumerate(((yes,no),(no,yes))):
            must_l=closure(a,y);must_r=closure(b,y)
            if z&must_l&must_r:continue
            eligible=[v for v in tables(a) if not y&~v]
            rec={'depth':depth,'left':a,'right':b,'NAND':bool(polarity),'distinct_small_tables':len(tables(a)),'yes':hex(y),'no':hex(z),'eligible':[hex(v) for v in sorted(eligible)]}
            summary.append(rec)
            if any(not reject(b,y,z&v,depth+1) for v in eligible):return False
    return True
assert reject(tuple(range(6)), F,universe^F,0)
print(json.dumps({'path_from_first':[[0,4,1,3],[0,2,2,1],[0,1,3,0],[4,5,0,3],[0,3,1,0],[1,2,1,1]],'ordered_wires':list(map(hex,wires)),'surviving_rectangles':summary},indent=2))
