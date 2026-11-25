"""Replay Res(XOR) certificates for BPHP(5,2) on all 1,024 assignments."""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path


@lru_cache(None)
def literal_truth(mask, rhs):
    return sum(1 << assignment for assignment in range(1024)
               if (mask & assignment).bit_count() % 2 == rhs)


def truth(clause):
    result = 0
    for mask, rhs in clause:
        result |= literal_truth(mask, rhs)
    return result


def integer(value, limit):
    if type(value) is not int or not 0 <= value < limit:
        raise ValueError(f'expected an integer in [0,{limit}), got {value!r}')
    return value


def replay_step(i, step, clauses):
    kind = step['rule']
    if kind == 'ax':
        p = integer(step['p'], 5)
        q = integer(step['q'], 5)
        hole = integer(step['hole'], 4)
        if p == q:
            raise ValueError('a collision axiom requires two distinct pigeons')
        clause = {(1 << (2 * pigeon + bit), 1 ^ ((hole >> bit) & 1))
                  for pigeon in (p, q) for bit in range(2)}
        return frozenset(clause), []
    if kind == 'res':
        neg = integer(step['neg'], i)
        pos = integer(step['pos'], i)
        pivot = integer(step['pivot'], 1024)
        if (pivot, 0) not in clauses[neg] or (pivot, 1) not in clauses[pos]:
            raise ValueError('a parent lacks its designated pivot equation')
        result = (clauses[neg] - {(pivot, 0)}) | (clauses[pos] - {(pivot, 1)})
        return result, [neg, pos]
    if kind == 'weak':
        parent = integer(step['parent'], i)
        result = set()
        for mask, rhs in step['clause']:
            if type(rhs) not in (int, bool) or rhs not in (0, 1):
                raise ValueError('a parity equation needs a Boolean right-hand side')
            result.add((integer(mask, 1024), int(rhs)))
        return frozenset(result), [parent]
    raise ValueError(f'unknown rule {kind!r}')


def audit(proof):
    if not isinstance(proof, list):
        raise ValueError('expected a chronological list of proof steps')
    clauses, tables, dependencies = [], [], []
    for index, step in enumerate(proof):
        try:
            clause, parents = replay_step(index, step, clauses)
            value = truth(clause)
            if parents:
                common = tables[parents[0]]
                for parent in parents[1:]:
                    common &= tables[parent]
                if common & ~value:
                    raise ValueError('parent truth tables do not imply the result')
        except (KeyError, ValueError, TypeError) as error:
            raise ValueError(f'line {index + 1}: {error}') from error
        clauses.append(clause)
        tables.append(value)
        dependencies.append(parents)
    if frozenset() not in clauses:
        raise ValueError('missing the syntactically empty clause')
    end = clauses.index(frozenset())
    live = {end}
    for index in reversed(range(end + 1)):
        if index in live:
            live.update(dependencies[index])
    return {'lines': len(proof), 'used': len(live), 'empty_line': end + 1,
            'distinct_syntactic_clauses': len(set(clauses)),
            'distinct_semantic_clauses': len(set(tables)),
            'rules': dict(Counter(step['rule'] for step in proof))}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).resolve().parent.parent / 'witness' / 'trace149.json')
    parser.add_argument('--expect-lines', type=int)
    args = parser.parse_args()
    try:
        result = audit(json.loads(args.certificate.read_text()))
        if args.expect_lines is not None and result['lines'] != args.expect_lines:
            raise ValueError(f"expected {args.expect_lines} lines, got {result['lines']}")
    except (OSError, ValueError) as error:
        parser.exit(1, f'{error}\n')
    print(json.dumps(result, sort_keys=True))
