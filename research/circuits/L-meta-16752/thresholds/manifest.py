"""Print a TSV of two-pin threshold matches for positive fixed split-literal desk rows."""
import argparse
import json
import re
import sys
from pathlib import Path

from threshold_minor import THRESHOLDS, threshold_minor


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('gaps', type=Path, help='downloaded public gaps.json export')
    args = parser.parse_args()
    rows = json.loads(args.gaps.read_bytes())['gaps']
    matches = []
    tables = set()
    row_id = re.compile(r'L-meta-(\d+)')
    literal = re.compile(r'Nat\.testBit \((\d+)\s*\*\s*2\s*\^\s*32\s*\+\s*(\d+)\)')
    for row in rows:
        statement = row.get('statement', '')
        identifier = row_id.fullmatch(row['id'])
        if not identifier or not statement.startswith('∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 '):
            continue
        if 'PEqualNP.MetaComplexity.Monotone2 C' not in statement:
            continue
        halves = literal.findall(statement)
        if len(halves) != 2 or halves[0] != halves[1]:
            continue
        high, low = map(int, halves[0])
        if max(high, low) >= (1 << 32):
            continue
        table = high << 32 | low
        tables.add(table)
        pair = threshold_minor(table)
        if pair:
            matches.append((int(identifier.group(1)), row['id'], table, THRESHOLDS[pair[1].image]))
    print('positive_id\ttable\tthreshold')
    for _, row, table, threshold in sorted(matches):
        print(f'{row}\t{table:#x}\t{threshold}')
    print(f'{len(tables)} distinct positive literal tables scanned', file=sys.stderr)


if __name__ == '__main__':
    main()
