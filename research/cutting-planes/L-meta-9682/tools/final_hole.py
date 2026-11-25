"""Exact final-hole obstruction under the public integer CP rules (four coordinates).

All CP lines use sum(coeff_i*x_i) >= rhs. See local-strategies.md for the proof
that the enumerated configurations cover *all* derivations of length <=15.
"""
from itertools import combinations
from math import gcd

ZERO = (0, 0, 0, 0, 0)
FALSE = (0, 0, 0, 0, 1)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def twice(a): return add(a,a)
def cut(a,d):
    assert d>0 and all(v%d==0 for v in a[:-1])
    return tuple(v//d for v in a[:-1])+(-((-a[-1])//d),)

def cuts(a):
    g=gcd(*a[:-1]); assert g or a[-1] == 0
    for d in range(2,g+1):
        if g%d == 0: yield cut(a,d)

EDGES=list(combinations(range(4),2))
AX=[(1,1,1,1,2)] + [tuple(-int(i in edge) for i in range(4))+(-1,) for edge in EDGES]
ALL=(1<<len(AX))-1
S=[ZERO]
for mask in range(1,ALL+1):
    bit=mask & -mask
    S.append(add(S[mask^bit],AX[bit.bit_length()-1]))

def subsets(mask):
    sub=mask
    while True:
        yield sub
        if sub==0:break
        sub=(sub-1)&mask

# Independent 16-line construction from the seven axioms. Triangle = {0,1,2},
# star = edges touching 3; both branches use axiom 0 (the total-size lower).
def witness():
    lines=AX[:]
    def plus(i,j):
        lines.append(add(lines[i],lines[j])); return len(lines)-1
    def div(i,d):
        lines.append(cut(lines[i],d)); return len(lines)-1
    e=lambda a,b:1+EDGES.index((a,b))
    tr=div(plus(plus(e(0,1),e(0,2)),e(1,2)),2)
    last_at_least=plus(0,tr)
    st=plus(plus(e(0,3),e(1,3)),e(2,3))
    last_at_most=div(plus(0,st),2)
    assert lines[plus(last_at_least,last_at_most)]==FALSE and len(lines)==16


def main():
    witness()
    checked={'doubled':0,'parallel':0,'nested':0}
    for a in range(1,ALL+1):
        for x in cuts(S[a]):
            for b in subsets(ALL^a):
                rest=S[ALL^a^b]
                # One cut and either a scalar two or a shared superexpression.
                assert add(twice(add(x,S[b])),rest)!=FALSE
                checked['doubled']+=1
                # The two unary nodes of an addition tree are either in separate
                # branches or one is an ancestor of the other.
                if b and a<b:
                    for y in cuts(S[b]):
                        assert add(add(x,y),rest)!=FALSE
                        checked['parallel']+=1
                for y in cuts(add(x,S[b])):
                    assert add(y,rest)!=FALSE
                    checked['nested']+=1
    print('checked shapes:',checked)
    print('Exact final-hole CP minimum: 16 lines (seven premises counted).')

if __name__=='__main__': main()
