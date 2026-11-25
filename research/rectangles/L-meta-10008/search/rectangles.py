"""Check mask-pair candidates or enumerate maximal empty rectangles using Python 3.10+."""
import argparse
from collections import Counter
from contextlib import nullcontext
import json
from pathlib import Path


DEFAULT = Path(__file__).with_name('partial20.json')


def validate_masks(masks, limit):
    if any(type(mask) is not int or not 0 <= mask <= limit for mask in masks):
        raise ValueError('mask outside the matrix')


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def verify(data, rows, full):
    covered = [0] * len(rows)
    rectangles = data['rectangles']
    for row_mask, col_mask in rectangles:
        validate_masks((row_mask, col_mask), full)
        for i in positions(row_mask):
            if rows[i] & col_mask:
                raise ValueError(f'rectangle covers a 1 in row {i}')
            covered[i] |= col_mask
    missing = [[i, j] for i, (ones, hits) in enumerate(zip(rows, covered))
               for j in positions(full & ~(ones | hits))]
    if 'missing' in data and missing != data['missing']:
        raise ValueError('missing-cell list disagrees with direct verification')
    zeros = sum((full ^ ones).bit_count() for ones in rows)
    return {'rectangles': len(rectangles), 'zeros': zeros,
            'covered_zeros': zeros - len(missing), 'missing': missing,
            'complete': not missing}


def enumerate_rectangles(rows, full, output):
    # Every maximal nonempty rectangle has a column set equal to the
    # intersection of the zero neighborhoods of its rows. Conversely each
    # such intersection closes to one maximal rectangle on taking all rows
    # that admit every selected column.
    neighborhoods = [full ^ ones for ones in rows]
    intersections = {full}
    for allowed in neighborhoods:
        intersections.update({mask & allowed for mask in intersections})
    areas = Counter()
    for columns in intersections:
        if not columns:
            continue
        row_mask = sum(1 << i for i, ones in enumerate(rows) if columns & ones == 0)
        if row_mask:
            areas[row_mask.bit_count() * columns.bit_count()] += 1
            if output is not None:
                print(row_mask, columns, file=output)
    return {'nonempty_maximal_rectangles': sum(areas.values()),
            'max_area': max(areas, default=0), 'area_histogram': dict(sorted(areas.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=DEFAULT,
                        help='JSON containing rows, plus rectangles for verification')
    commands = parser.add_subparsers(dest='command', required=True)
    check = commands.add_parser('verify')
    check.add_argument('--require-cover', action='store_true')
    enum = commands.add_parser('enumerate')
    enum.add_argument('--emit', type=Path, help='write all maximal row/column mask pairs')
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    rows = data['rows']
    full = (1 << len(rows)) - 1
    validate_masks(rows, full)
    if args.command == 'verify':
        result = verify(data, rows, full)
        print(json.dumps(result))
        return int(args.require_cover and not result['complete'])
    with args.emit.open('w') if args.emit else nullcontext() as output:
        print(json.dumps(enumerate_rectangles(rows, full, output)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
