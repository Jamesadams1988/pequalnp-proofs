"""Read-once resolution for the all-but-one-positive column subproblem."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


def cell(p, h):
    return 1 + 4*p + h


def hall(s, t):
    return frozenset(cell(p,h) for p in s for h in range(4) if h not in t)


def block(s, t, h):
    steps, lines = [], []

    def add(step, c):
        steps.append(step)
        lines.append(frozenset(c))
        return len(lines)-1

    def resolve(pos, neg, r):
        x = cell(r,h)
        assert x in lines[pos] and -x in lines[neg]
        return add({'rule':'res','pos':pos,'neg':neg,'pivot':x-1},
                   (lines[pos]-{x}) | (lines[neg]-{-x}))

    predecessors = {r:add({'rule':'prior','missing':r}, hall(s-{r}, t-{h})) for r in sorted(s)}
    pairs = {(i,j):add({'rule':'hole','p':i,'q':j,'h':h}, {-cell(i,h),-cell(j,h)})
             for i,j in combinations(sorted(s),2)}

    def recur(active):
        r = active[-1]
        if len(active) == 1:
            return predecessors[r]
        neg = predecessors[r]
        for i in active[:-1]:
            neg = resolve(neg, pairs[i,r], i)
        pos = recur(active[:-1])
        return resolve(pos, neg, r)

    root = recur(sorted(s))
    assert lines[root] == hall(s,t)
    assert root == len(steps)-1 and len(set(lines)) == len(lines)
    n_inputs = len(predecessors) + len(pairs)
    assert len(steps) == 2*n_inputs-1
    uses = Counter(i for st in steps if st['rule']=='res' for i in (st['pos'],st['neg']))
    assert uses == Counter(range(root))

    # A model falsifying the target and just the one designated source.
    for i,step in enumerate(steps[:n_inputs]):
        if step['rule']=='prior':
            on = {cell(step['missing'], h)}
        else:
            on = {cell(step['p'],h), cell(step['q'],h)}
        def sat(c):
            return any((abs(lit) in on) == (lit>0) for lit in c)
        assert not sat(lines[root])
        assert [j for j in range(n_inputs) if not sat(lines[j])] == [i]
    return steps


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-trace',type=Path,help='write the 5-variable local root example on hole 0')
    opts = parser.parse_args()
    for k in range(1,5):
        count = 0
        for s in combinations(range(5), k+1):
            for t in combinations(range(4), k):
                for h in t:
                    steps = block(set(s),set(t),h)
                    joins = sum(st['rule']=='res' for st in steps)
                    assert joins == (k+1)*(k+2)//2-1
                    count += 1
        print(f'k={k}: {joins} binary resolutions per column block, {count} lifted block choices verified')
    if opts.root_trace:
        opts.root_trace.write_text(json.dumps(block(set(range(5)),set(range(4)),0),indent=2)+'\n')


if __name__=='__main__':
    main()
