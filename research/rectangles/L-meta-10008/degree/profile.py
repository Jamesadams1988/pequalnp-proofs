"""Sharp local row-degree profile for the 31-point incidence matrix."""
from itertools import combinations
from pathlib import Path
import json


def members(mask):
    return [i for i in range(31) if mask >> i & 1]


def profile(m, rows):
    # Take disjoint sections of the six lines through point 0. Four
    # coordinates encode up to six points by their distinct two-element codes.
    pencil = members(rows[0])
    lines = [[p for p, v in enumerate(rows) if v >> j & 1] for j in pencil]
    sections = [lines[0]] + [[p for p in line if p != 0] for line in lines[1:]]
    assert sorted(p for section in sections for p in section) == list(range(31))
    boxes = []
    included = []
    budget = m
    for section in sections:
        if budget < 4:
            for p in section[:budget]:
                included.append(p)
                boxes.append(1 << p)
            break
        included.extend(section)
        codes = list(combinations(range(4), 2))[:len(section)]
        for i in range(4):
            boxes.append(sum(1 << p for p, code in zip(section, codes) if i in code))
        budget -= 4
    rectangle_masks = []
    for support in boxes:
        forbidden = 0
        for p in members(support):
            forbidden |= rows[p]
        rectangle_masks.append((support, ((1 << 31)-1) ^ forbidden))
    for p in included:
        covering = [b for a,b in rectangle_masks if a >> p & 1]
        union = 0
        for b in covering:
            union |= b
        assert 1 <= len(covering) <= 2 and union == ((1 << 31)-1) ^ rows[p]
    limit = m if m < 4 else min(31, m + m // 4 + 1)
    assert len(set(included)) == len(included) == limit and len(boxes) <= m
    return len(included), included, rectangle_masks


def main():
    rows = json.loads(Path(__file__).with_name("rows.json").read_text())
    columns = [sum(1 << p for p in range(31) if rows[p] >> j & 1) for j in range(31)]
    for name, matrix in (("row", rows), ("column", columns)):
        assert all(a.bit_count() == 6 for a in matrix)
        assert all((a & b).bit_count() == 1 for a,b in combinations(matrix, 2))
        values = [profile(m, matrix)[0] for m in range(25)]
        print(name, "maximum selectable vertices at degree at most two for budgets 0..24:", values)
        assert values[17] == 22 and values[23] == 29 and values[24] == 31


if __name__ == "__main__":
    main()
