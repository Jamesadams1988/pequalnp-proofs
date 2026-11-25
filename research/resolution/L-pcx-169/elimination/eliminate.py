"""Ordered Davis–Putnam resolution on unary PHP(5,4), with subsumption."""
import argparse
import json
import random
from itertools import combinations
from pathlib import Path


N = 20


class Search:
    def __init__(self):
        self.ids, self.clauses, self.steps, self.parents = {}, [], [], []
        self.ancestry = []
        for p in range(5):
            self.line(15 << (4*p), {"rule": "pigeon", "p": p})
        for p, q in combinations(range(5), 2):
            for h in range(4):
                self.line(((1 << (4*p+h)) | (1 << (4*q+h))) << N,
                          {"rule": "hole", "p": p, "q": q, "h": h})

    def line(self, clause, step):
        if clause in self.ids:
            return self.ids[clause]
        i = self.ids[clause] = len(self.clauses)
        self.clauses.append(clause)
        self.steps.append(step)
        self.parents.append([] if step["rule"] != "res" else [step["pos"], step["neg"]])
        ancestry = 1 << i
        for parent in self.parents[i]:
            ancestry |= self.ancestry[parent]
        self.ancestry.append(ancestry)
        return i

    def close(self, v, active, rng):
        pv, nv = 1 << v, 1 << (v + N)
        yes = [c for c in active if c & pv]
        no = [c for c in active if c & nv]
        others = [c for c in active if not c & (pv | nv)]
        if len(yes)*len(no) > 20000:
            return None
        generated = {}
        rng.shuffle(yes)
        rng.shuffle(no)
        for a in yes:
            for b in no:
                r = (a ^ pv) | (b ^ nv)
                if (r & (r >> N)) != 0:
                    continue
                cost = (self.ancestry[self.ids[a]] | self.ancestry[self.ids[b]]).bit_count()
                if r not in generated or cost < generated[r][0]:
                    generated[r] = (cost, a, b)
        candidates = set(others) | generated.keys()
        if len(candidates) > 2200:
            return None
        result = []
        for c in sorted(candidates, key=lambda c: (c.bit_count(), c)):
            if any((e & c) == e for e in result):
                continue
            if c not in self.ids:
                _, a, b = generated[c]
                self.line(c, {"rule": "res", "pos": self.ids[a], "neg": self.ids[b], "pivot": v})
            result.append(c)
        if len(result) > 400:
            return None
        return result

    def trace(self):
        keep = set()
        todo = [self.ids[0]]
        while todo:
            i = todo.pop()
            if i not in keep:
                keep.add(i)
                todo.extend(self.parents[i])
        renumber = {k: n for n, k in enumerate(sorted(keep))}
        trace = [dict(self.steps[k]) for k in sorted(keep)]
        for s in trace:
            if s['rule'] == 'res':
                s['pos'] = renumber[s['pos']]
                s['neg'] = renumber[s['neg']]
        return trace


def run(order, seed):
    search, rng = Search(), random.Random(seed)
    active = search.clauses[:]
    for v in order:
        active = search.close(v, active, rng)
        if active is None:
            return None
        if 0 in active:
            return search.trace()


def verify(trace):
    # Replay independently using ordinary signed-literal sets.
    lines = []
    for step in trace:
        if step['rule'] == 'pigeon':
            p = step['p']
            assert 0 <= p < 5
            c = {4*p+h+1 for h in range(4)}
        elif step['rule'] == 'hole':
            p, q, h = step['p'], step['q'], step['h']
            assert 0 <= p < q < 5 and 0 <= h < 4
            c = {-1-4*p-h, -1-4*q-h}
        else:
            assert step['rule'] == 'res'
            p, q = step['pos'], step['neg']
            assert 0 <= p < len(lines) and 0 <= q < len(lines)
            v = 1+step['pivot']
            assert 1 <= v <= N and v in lines[p] and -v in lines[q]
            c = (lines[p]-{v}) | (lines[q]-{-v})
        lines.append(c)
    assert lines and not lines[-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds', type=int, default=100)
    parser.add_argument('--seed', type=int, default=169)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    best = 10000
    col = sorted(range(20), key=lambda v: (v%4, v//4))
    for i in range(args.rounds):
        if i % 4 == 0:
            order = list(range(20))
        elif i % 4 == 1:
            order = col[:]
        elif i % 4 == 2:
            order = sum((rng.sample(range(4*p, 4*p+4),4) for p in range(5)), [])
        else:
            order = sum((rng.sample(range(h,20,4),5) for h in range(4)), [])
        if i > 3:
            for _ in range(rng.randrange(6)):
                j = rng.randrange(19)
                order[j], order[j+1] = order[j+1], order[j]
        trace = run(order, rng.randrange(1 << 32))
        if trace and len(trace) < best:
            verify(trace)
            best = len(trace)
            print(f"{best} lines in trial {i}: {order}", flush=True)
            if args.output:
                args.output.write_text(json.dumps(trace, separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
