"""Encode the four-variable, one-pair conversion with a prescribed line budget as CNF.

python3 pair_minimum.py 10 pair10.cnf
cadical pair10.cnf
"""
import argparse
from itertools import combinations
from pathlib import Path


class Formula:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def one(self, n):
        outcomes = [self.var() for _ in range(n)]
        self.clauses.append(outcomes)
        self.clauses.extend([-a, -b] for a, b in combinations(outcomes, 2))
        return outcomes

    def eq_if(self, condition, x, y):
        self.clauses.extend(([-condition, x, -y], [-condition, -x, y]))

    def select(self, selectors, values):
        x = self.var()
        for condition, value in zip(selectors, values):
            self.eq_if(condition, x, value)
        return x

    def save(self, output):
        output.write_text(f"p cnf {self.n} {len(self.clauses)}\n" +
                          "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses))


def encode(budget):
    f = Formula()
    q = [(m, b) for m in range(1, 16) for b in (0, 1)]
    lines, bad = [], []
    diagonal = [0, 5, 10, 15]
    for k in range(budget):
        row = {form: f.var() for form in q}
        lines.append(row)
        falsified = [f.var() for _ in range(16)]
        bad.append(falsified)
        for x, fx in enumerate(falsified):
            sat_literals = [row[m, b] for m, b in q if (m & x).bit_count() % 2 == b]
            # Row is false iff no present equation is satisfied.
            f.clauses.extend([-fx, -lit] for lit in sat_literals)
            f.clauses.append([fx, *sat_literals])
            if x not in diagonal:
                f.clauses.append([-fx])
        # Tautological lines are dispensable: a resolvent of a tautology is
        # a semantic weakening of its other parent.
        f.clauses.append([falsified[x] for x in diagonal])
        if k < 4:
            want = {(1 << (2*p+b), 1 - (k >> b & 1)) for p in (0, 1) for b in (0, 1)}
        elif k == budget - 1:
            want = {(5, 1), (10, 1)}
        else:
            want = None
        if want is not None:
            f.clauses.extend([lit if key in want else -lit] for key, lit in row.items())
        if k < 4:
            continue
        res = f.var()
        left = f.one(k)
        right = f.one(k)
        pivot = [None, *f.one(15)]
        for i in range(k):
            # On a weakening, false on the child implies false on selected parent.
            for x in diagonal:
                f.clauses.append([res, -left[i], -falsified[x], bad[i][x]])
            # Resolving a single row with itself would require it to be tautological.
            f.clauses.append([-res, -left[i], -right[i]])
        for m, b in q:
            lq = f.select(left, [lines[i][m, b] for i in range(k)])
            rq = f.select(right, [lines[i][m, b] for i in range(k)])
            erase = lq if b == 0 else rq
            retain = rq if b == 0 else lq
            cq = row[m, b]
            query = pivot[m]
            f.clauses.extend([
                [-res, -query, erase],
                [-res, -retain, cq],
                [-res, query, -erase, cq],
                [-res, -cq, retain, erase],
                [-res, -cq, retain, -query],
            ])
    return f


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("budget", type=int)
    parser.add_argument("output", type=Path)
    opts = parser.parse_args()
    assert opts.budget >= 5
    encode(opts.budget).save(opts.output)
