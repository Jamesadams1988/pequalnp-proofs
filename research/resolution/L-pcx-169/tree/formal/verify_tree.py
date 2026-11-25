"""Replay the chronological ordinary-resolution certificate for unary PHP(5,4)."""
import argparse
from collections import Counter
import json
from pathlib import Path


def bounded(value, bound):
    if type(value) is not int or not 0 <= value < bound:
        raise ValueError(f'expected an integer in [0, {bound}), got {value!r}')
    return value


def inspect(steps):
    clauses = []
    readers = Counter()
    rules = Counter()
    for index, step in enumerate(steps):
        rule = step['rule']
        rules[rule] += 1
        if rule == 'pigeon':
            pigeon = bounded(step['p'], 5)
            result = {(4 * pigeon + hole, True) for hole in range(4)}
        elif rule == 'hole':
            p, q = bounded(step['p'], 5), bounded(step['q'], 5)
            h = bounded(step['h'], 4)
            if p == q:
                raise ValueError(f'line {index + 1} repeats one pigeon in a collision')
            result = {(4 * p + h, False), (4 * q + h, False)}
        elif rule == 'res':
            neg = bounded(step['neg'], index)
            pos = bounded(step['pos'], index)
            pivot = bounded(step['pivot'], 20)
            if (pivot, False) not in clauses[neg] or (pivot, True) not in clauses[pos]:
                raise ValueError(f'line {index + 1} has an invalid signed pivot')
            result = (clauses[pos] - {(pivot, True)}) | (clauses[neg] - {(pivot, False)})
            readers.update((pos, neg))
        else:
            raise ValueError(f'line {index + 1} uses unknown rule {rule!r}')
        clauses.append(frozenset(result))
    if not clauses or clauses[-1]:
        raise ValueError('the final line must be the empty clause')
    # All parent indices are strictly earlier, so one use for every nonroot
    # occurrence makes the dependency graph a single tree with the last root.
    tree = all(readers[i] == 1 for i in range(len(clauses) - 1))
    return {'lines': len(steps), 'pigeon_axioms': rules['pigeon'], 'hole_axioms': rules['hole'],
            'leaves': rules['pigeon'] + rules['hole'], 'resolutions': rules['res'],
            'distinct_clauses': len(set(clauses)), 'tree': tree}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--expect-377-tree', action='store_true')
    args = parser.parse_args()
    try:
        stats = inspect(json.loads(args.certificate.read_text()))
        if args.expect_377_tree and (stats['lines'], stats['leaves'], stats['resolutions'], stats['tree']) != (377, 189, 188, True):
            raise ValueError('the certificate does not have the advertised 377-node tree shape')
    except (KeyError, TypeError, ValueError, OSError) as error:
        parser.exit(1, f'{error}\n')
    print(json.dumps(stats, sort_keys=True))
