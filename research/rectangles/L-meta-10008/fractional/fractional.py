"""Exact rational optimum of the fractional cover relaxation for the cyclic matrix."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json

N = 31
ALL = (1 << N) - 1


def six_by_ten(rows):
    for points in combinations(range(N), 6):
        forbidden = 0
        for i in points:
            forbidden |= rows[i]
        allowed = ALL ^ forbidden
        if allowed.bit_count() == 10:
            yield points, allowed


def main():
    rows = json.loads((Path(__file__).resolve().parent.parent / "degree" / "rows.json").read_text())
    incidence = [[0] * N for i in range(N)]
    count = 0
    for points, allowed in six_by_ten(rows):
        count += 1
        cols = [j for j in range(N) if allowed >> j & 1]
        for i in points:
            for j in cols:
                incidence[i][j] += 1
    rates = {incidence[i][j] for i in range(N) for j in range(N) if not rows[i] >> j & 1}
    assert count == 3100 and rates == {240}
    assert all(incidence[i][j] == 0 for i in range(N) for j in range(N) if rows[i] >> j & 1)
    assert Fraction(count,240) == Fraction(775,60) == Fraction(155,12)
    print("3,100 all-zero 6-by-10 rectangles. Each zero cell occurs exactly 240 times.")
    print("Unit edge demand with uniform weight 1/240 costs 155/12; area at most 60 gives the matching dual.")


if __name__ == "__main__":
    main()
