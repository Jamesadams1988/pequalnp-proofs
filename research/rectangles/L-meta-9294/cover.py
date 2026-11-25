"""Compute the minimum all-one rectangle cover and maximum fooling set for L-meta-9294.

Run `python3 cover.py` with Python 3.10+. Use `--output result.json` to save the
witnesses. Coordinates are zero-based. Bit j of each row mask is column j.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path

ROWS = [126, 413, 683, 839, 483, 725, 825, 822, 730, 492]
SIZE = len(ROWS)


def cells(row_mask, column_mask):
    return sum(column_mask << (SIZE * i) for i in range(SIZE) if row_mask >> i & 1)


def maximal_rectangles():
    # Any nonempty all-one rectangle can be extended to a maximal one.
    # Its maximal column set is an intersection of row neighborhoods.
    intersections = {(1 << SIZE) - 1}
    for row in ROWS:
        intersections.update({row & columns for columns in intersections})
    rectangles = []
    for columns in sorted(intersections - {0}):
        rows = sum(1 << i for i, ones in enumerate(ROWS) if columns & ~ones == 0)
        if rows:
            rectangles.append((rows, columns))
    return rectangles


def minimum_cover(boxes, target):
    masks = [cells(*box) for box in boxes]
    max_area = max(mask.bit_count() for mask in masks)
    incident = [[k for k, mask in enumerate(masks) if mask >> pos & 1]
                for pos in range(SIZE ** 2)]

    @lru_cache(None)
    def search(uncovered, budget):
        if not uncovered:
            return ()
        need = uncovered.bit_count()
        gains = [(mask & uncovered).bit_count() for mask in masks]
        # Even disjoint gains cannot cover `need` cells in this budget.
        if budget == 0 or sum(sorted(gains, reverse=True)[:budget]) < need:
            return None
        # Every member of a successful cover must contribute enough cells
        # for the other budget-1 rectangles to cover the rest.
        min_gain = need - max_area * (budget - 1)
        chosen = None
        for i in range(SIZE ** 2):
            if uncovered >> i & 1:
                choices = [k for k in incident[i] if gains[k] >= min_gain]
                if chosen is None or len(choices) < len(chosen):
                    chosen = choices
        # A cover must contain at least one rectangle on the chosen cell.
        for k in sorted(chosen, key=gains.__getitem__, reverse=True):
            tail = search(uncovered & ~masks[k], budget - 1)
            if tail is not None:
                return (k, *tail)
        return None

    first_budget = (target.bit_count() + max_area - 1) // max_area
    logs = []
    for budget in range(first_budget, SIZE + 1):
        chosen = search(target, budget)
        logs.append({'budget': budget, 'exists': chosen is not None,
                     'cumulative_memoized_states': search.cache_info().currsize})
        if chosen is not None:
            result = [boxes[k] for k in chosen]
            union = 0
            for box in result:
                union |= cells(*box)
            if union != target or len(result) != budget:
                raise ValueError('invalid cover witness')
            return result, logs
    raise ValueError('the single-row cover guarantees this search succeeds')


def maximum_fooling_set():
    # Two ones are incompatible if an all-one rectangle cannot contain both.
    points = [(i, j) for i, row in enumerate(ROWS) for j in range(SIZE) if row >> j & 1]
    neighbors = [sum(1 << k for k, (r, c) in enumerate(points)
                     if not (ROWS[i] >> c & 1 and ROWS[r] >> j & 1)) for i, j in points]
    best = []

    def extend(chosen, available):
        nonlocal best
        if len(chosen) > len(best):
            best = chosen
        while len(chosen) + available.bit_count() > len(best):
            bit = available & -available
            index = bit.bit_length() - 1
            available ^= bit
            extend(chosen + [index], available & neighbors[index])

    extend([], (1 << len(points)) - 1)
    return [points[k] for k in best]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='also write the JSON report here')
    args = parser.parse_args()
    boxes = maximal_rectangles()
    target = sum(row << (SIZE * i) for i, row in enumerate(ROWS))
    histogram = Counter(a.bit_count() * b.bit_count() for a, b in boxes)
    witness, searches = minimum_cover(boxes, target)
    fooling = maximum_fooling_set()
    result = {'rows': ROWS, 'one_entries': target.bit_count(), 'maximal_rectangles': len(boxes),
              'area_histogram': dict(sorted(histogram.items())), 'searches': searches,
              'minimum_cover': len(witness), 'mask_pairs': witness,
              'maximum_fooling_set': len(fooling), 'fooling_cells': fooling}
    report = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(report)
    print(report, end='')


if __name__ == '__main__':
    main()
