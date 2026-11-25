"""Write a candidate witness TSV for generate_exact.py from the threshold rows.

    python3 tree_replay.py > candidates.tsv
    python3 generate_exact.py --rows ../thresholds/rows.tsv --family candidates.tsv

Requires Python 3.10+ and a C++20 compiler. A ">9" entry means all monotone
AND/OR trees through nine gates were exhausted for that mask.
"""
import argparse
import ast
import csv
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
INPUTS = {f'x{i}': sum(1 << r for r in range(64) if (r >> i) & 1)
          for i in range(6)}


def read_targets(path):
    with path.open(newline='') as source:
        rows = [(int(r['table'], 16), r['positive_id'])
                for r in csv.DictReader(source, delimiter='\t')]
    if any(not 0 <= mask < 1 << 64 or not name for mask, name in rows):
        raise ValueError('expected six-input masks and nonempty row IDs')
    if len({mask for mask, _ in rows}) != len(rows) or len({name for _, name in rows}) != len(rows):
        raise ValueError('duplicate row ID or truth table')
    # Keep generated Lean declarations in the published mask order.
    return sorted(rows)


def evaluate(node):
    """Return the full truth table, gate count and depth of a positive tree."""
    if isinstance(node, ast.Name) and node.id in INPUTS:
        return INPUTS[node.id], 0, 0
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, (ast.BitAnd, ast.BitOr)):
        raise ValueError('unexpected expression in tree witness')
    left, left_size, left_depth = evaluate(node.left)
    right, right_size, right_depth = evaluate(node.right)
    mask = left & right if isinstance(node.op, ast.BitAnd) else left | right
    return mask, 1 + left_size + right_size, 1 + max(left_depth, right_depth)


def replay(rows, compiler):
    with TemporaryDirectory() as tmp:
        executable = Path(tmp) / 'trees'
        subprocess.run([compiler, '-O3', '-std=c++20', HERE / 'trees.cpp', '-o', executable],
                       check=True)
        result = subprocess.run([executable], input=''.join(f'{m:x}\n' for m, _ in rows),
                                text=True, stdout=subprocess.PIPE, check=True)
    verified = []
    for (target, name), line in zip(rows, result.stdout.splitlines(), strict=True):
        mask, *answer = line.split('\t')
        if int(mask, 16) != target:
            raise ValueError(f'{name}: unexpected mask {mask}')
        if answer == ['>9']:
            verified.append((name, hex(target), '>9', '', ''))
        else:
            gates, depth, witness = answer
            size = int(gates)
            metrics = evaluate(ast.parse(witness, mode='eval').body)
            if not 0 <= size <= 9 or metrics != (target, size, int(depth)):
                raise ValueError(f'{name}: witness disagrees with its mask, gate count or depth')
            verified.append((name, hex(target), gates, depth, witness))
    return verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows', type=Path, default=HERE.parent / 'thresholds' / 'rows.tsv')
    parser.add_argument('--cxx', default='c++', help='C++20 compiler executable')
    args = parser.parse_args()
    results = replay(read_targets(args.rows), args.cxx)
    writer = csv.writer(sys.stdout, delimiter='\t', lineterminator='\n')
    writer.writerow(['positive_row', 'mask', 'minimum_monotone_tree_gates', 'depth', 'witness'])
    writer.writerows(results)
    hits = sum(bool(r[-1]) for r in results)
    print(f'{hits} rows have a tree through nine gates; {len(results) - hits} exceed nine.',
          file=sys.stderr)


if __name__ == '__main__':
    main()
