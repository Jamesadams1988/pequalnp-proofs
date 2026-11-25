"""Audit one filtered bipartite rectangle alongside unshared direct stars.

edges.json numbers both 20-vertex classes from 0. Every chosen rectangle with two
distinct active centers is accounted for; arbitrary singleton-center cases have
the ordinary star bound. The two filter gates are treated as free.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
N = 20

def matching(edges):
    """A maximum unit-capacity bipartite matching, represented as line -> point."""
    by_point = [sorted(l for p,l in edges if p==i) for i in range(N)]
    owner = {}
    def augment(p,seen):
        for l in by_point[p]:
            if l in seen:
                continue
            seen.add(l)
            if l not in owner or augment(owner[l],seen):
                owner[l]=p
                return True
        return False
    for p in range(N):
        augment(p,set())
    return owner

def nonempty_subsets(xs):
    return [set(s) for r in range(1,len(xs)+1) for s in combinations(sorted(xs),r)]

def run(edges):
    points = [{l for p,l in edges if p==i} for i in range(N)]
    lines = [{p for p,l in edges if l==i} for i in range(N)]
    assert all(len(a&b)<=1 for a,b in combinations(points,2))
    assert all(len(a&b)<=1 for a,b in combinations(lines,2))
    copies=Counter(edges)
    dup={(p,l) for p,l in edges if len(points[p])==4 and len(lines[l])==4}
    assert len(dup)==5
    copies.update(dup)
    matchings=[]
    while copies:
        chosen=matching(copies)
        assert len(chosen)==N
        schedule=[next(l for l,p in chosen.items() if p==v) for v in range(N)]
        matchings.append(schedule)
        for p,l in enumerate(schedule):
            copies[p,l]-=1
            if not copies[p,l]:
                del copies[p,l]
    assert len(matchings)==5 and set(edges)=={(p,l) for m in matchings for p,l in enumerate(m)}
    minima=Counter()
    for p,l in sorted(edges):
        for pp in nonempty_subsets(lines[l]-{p}):
            for ll in nonempty_subsets(points[p]-{l}):
                # A={p}+pp, B={l}+ll, D meets A and B only at p,l.
                hit={(p,l)}|{(x,l) for x in pp}|{(p,y) for y in ll}
                assert not any((x,y) in edges for x in pp for y in ll)
                rem=edges-hit
                residual_cover=len(matching(rem))
                raw_rect_cost=len(pp)+len(ll)+1
                assert raw_rect_cost==len(hit)
                # Direct-star cover costs |rem| + tau(rem) - 1; combine with one OR.
                minima[raw_rect_cost+len(rem)+residual_cover]+=1
    return matchings, sorted(dup), dict(sorted(minima.items()))

if __name__=='__main__':
    es=set(map(tuple,json.loads((HERE/'edges.json').read_text())))
    assert len(es)==95
    perms,extra,costs=run(es)
    print('parallel copies:',extra)
    print('perfect matching family:',json.dumps(perms))
    print('fully filtered double stars:',sum(costs.values()))
    print('full circuit costs with free marking and filtering:',costs)
    assert min(costs)>=114
