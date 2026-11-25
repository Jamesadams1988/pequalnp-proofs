"""Try to improve a partial cover by moving rectangles onto uncovered cells."""
import argparse
import json
from pathlib import Path
import random
from rectangles import DEFAULT, positions, verify


def maximal(rows, columns, row_mask, col_mask, close_rows_first):
    def common(mask, opposite):
        return sum(1 << i for i, forbidden in enumerate(opposite) if not mask & forbidden)

    if close_rows_first:
        row_mask = common(col_mask, rows)
    col_mask = common(row_mask, columns)
    return row_mask if close_rows_first else common(col_mask, rows), col_mask


def search(rows, seed, count, steps, rng):
    full = (1 << len(rows)) - 1
    columns = [sum(1 << i for i in range(len(rows)) if rows[i] >> j & 1)
               for j in range(len(rows))]
    best = None
    best_size = len(rows) ** 2 + 1
    rectangles = list(seed[:count])
    for step in range(steps + 1):
        hits = [0] * len(rows)
        multiple = [0] * len(rows)
        for row_mask, col_mask in rectangles:
            for i in positions(row_mask):
                multiple[i] |= hits[i] & col_mask
                hits[i] |= col_mask
        missing = [full & ~(occupied | ones) for occupied, ones in zip(hits, rows)]
        unique = [occupied & ~shared for occupied, shared in zip(hits, multiple)]
        cells = [(i, j) for i, mask in enumerate(missing) for j in positions(mask)]
        if len(cells) < best_size:
            best, best_size = list(rectangles), len(cells)
        if not cells or step == steps:
            break
        i, j = rng.choice(cells)
        options = []
        for index, (row_mask, col_mask) in enumerate(rectangles):
            # Remove every row or column incompatible with the target cell.
            reduced_rows = (row_mask & ~columns[j]) | (1 << i)
            reduced_cols = (col_mask & ~rows[i]) | (1 << j)
            for first in (False, True):
                new_rows, new_cols = maximal(rows, columns, reduced_rows, reduced_cols, first)
                gained = sum((missing[p] & new_cols).bit_count() for p in positions(new_rows))
                lost = sum((unique[p] & col_mask & ~(new_cols if new_rows >> p & 1 else 0)).bit_count()
                           for p in positions(row_mask))
                options.append((gained - lost + rng.random(), index, (new_rows, new_cols)))
        _, changed, replacement = rng.choice(options) if rng.randrange(30) == 0 else max(options)
        rectangles[changed] = replacement
        if step % 1000 == 999:
            rectangles = list(best)
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=DEFAULT)
    parser.add_argument('--count', type=int, default=20)
    parser.add_argument('--steps', type=int, default=1000)
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    rows, initial = data['rows'], data['rectangles']
    full = (1 << len(rows)) - 1
    verify(data, rows, full)
    if not 1 <= args.count <= len(initial) or args.steps < 0:
        parser.error('choose a positive count at most the input length and nonnegative steps')
    candidate = {'rows': rows, 'rectangles': search(rows, initial, args.count, args.steps,
                                                    random.Random(args.seed))}
    result = verify(candidate, rows, full)
    candidate['missing'] = result['missing']
    if args.output:
        args.output.write_text(json.dumps(candidate, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
