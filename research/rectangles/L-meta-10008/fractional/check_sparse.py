"""Directly expand every translated rectangle and count coverage of the literal matrix."""
from pathlib import Path
from fractions import Fraction
import json

here = Path(__file__).resolve().parent
rows = json.loads((here.parent / "degree" / "rows.json").read_text())
certificate = json.loads((here / "sparse.json").read_text())
matrix = [[0] * 31 for _ in rows]
total = 0
for rowset, colset, weight in certificate["orbits"]:
    assert 0 < rowset < 2**31 and 0 < colset < 2**31 and weight > 0
    for shift in range(31):
        for i in range(31):
            if rowset >> ((i-shift) % 31) & 1:
                for j in range(31):
                    if colset >> ((j-shift) % 31) & 1:
                        matrix[i][j] += weight
        total += weight
den = certificate["multiplicity"]
assert all(matrix[i][j] == (0 if rows[i] >> j & 1 else den)
           for i in range(31) for j in range(31))
assert Fraction(total, den) == Fraction(155, 12)
print(f"{total} weighted translates. Every zero is covered {den} times; every one zero times.")
