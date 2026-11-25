"""Rebuild the C6 encoding, replay its RUP proof, and check the five-OR witness."""
import gzip
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EDGES = [(i, (i + 1) % 6) for i in range(6)]


def rebuild():
    clauses = []
    count = 0
    def variable():
        nonlocal count
        count += 1
        return count
    def add(*literals):
        clauses.append(literals)
    def conjunction(literals):
        result = variable()
        for literal in literals:
            add(-result, literal)
        add(result, *[-literal for literal in literals])
        return result
    def selector(width):
        selected = [variable() for _ in range(width)]
        add(*selected)
        return selected
    def evaluate(selected, assignment, previous):
        tests = [-selected[i] for i in range(6) if not (assignment >> i & 1)]
        for pick, wire in zip(selected[6:], previous):
            tests.append(-conjunction([pick, -wire]))
        return conjunction(tests)

    positive = [(1 << a) | (1 << b) for a, b in EDGES]
    def independent(x):
        return all(x & edge != edge for edge in positive)
    negative = [x for x in range(64) if independent(x) and
                all(not independent(x | (1 << i)) for i in range(6) if not (x >> i & 1))]
    samples = positive + negative
    values = [[] for _ in samples]
    for level in range(4):
        left, right = selector(6 + level), selector(6 + level)
        # Symmetry break: most significant differing selector bit is zero on the left.
        equal_prefix = None
        for u, v in reversed(list(zip(left, right))):
            condition = [] if equal_prefix is None else [-equal_prefix]
            add(*condition, -u, v)
            equal = variable()
            if equal_prefix is not None:
                add(-equal, equal_prefix)
            add(-equal, -u, v)
            add(-equal, u, -v)
            add(*condition, -u, -v, equal)
            add(*condition, u, v, equal)
            equal_prefix = equal
        for j, assignment in enumerate(samples):
            a = evaluate(left, assignment, values[j])
            b = evaluate(right, assignment, values[j])
            result = variable()
            add(-a, result)
            add(-b, result)
            add(-result, a, b)
            values[j].append(result)
    final = selector(10)
    for j, assignment in enumerate(samples):
        output = evaluate(final, assignment, values[j])
        add(output if j < len(positive) else -output)
    return count, clauses, positive, negative


def replay():
    num_vars, clauses, positive, negative = rebuild()
    expected = f'p cnf {num_vars} {len(clauses)}\n'
    expected += ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)
    assert gzip.decompress((ROOT / 'cycle6-4.cnf.gz').read_bytes()) == expected.encode()
    db = {i: c for i, c in enumerate(clauses, 1)}
    steps = 0
    empty = False
    with gzip.open(ROOT / 'cycle6-4.lrat.gz', 'rt') as proof:
        for line in proof:
            tokens = line.split()
            if tokens[1] == 'd':
                assert tokens[-1] == '0'
                for token in tokens[2:-1]:
                    del db[int(token)]
                continue
            data = list(map(int, tokens))
            end = data.index(0)
            index, clause, hints = data[0], tuple(data[1:end]), data[end+1:-1]
            assert data[-1] == 0 and index not in db
            assert all(0 < abs(z) <= num_vars for z in clause) and all(h in db for h in hints)
            true_literals = {-literal for literal in clause}
            for h in hints:
                previous = db[h]
                assert all(z not in true_literals for z in previous)
                open_literals = [z for z in previous if -z not in true_literals]
                assert len(open_literals) <= 1
                if not open_literals:
                    break
                true_literals.add(open_literals[0])
            else:
                raise ValueError(f'No unit-propagation contradiction at proof line {index}')
            db[index] = clause
            steps += 1
            empty |= not clause
    assert empty
    print(f'Four ORs excluded: {num_vars} variables, {len(clauses)} clauses, '
          f'{steps} RUP additions, empty clause verified.')
    print(f'Boundary assignments: {len(positive)} minimal true and {len(negative)} maximal false.')


def witness():
    program = json.loads((ROOT / 'cycle6-5.json').read_text())
    assert list(map(tuple, program['edges'])) == EDGES and len(program['or_operands']) == 5
    for x in range(64):
        wires = [bool(x >> i & 1) for i in range(6)]
        for left, right in program['or_operands']:
            assert all(0 <= i < len(wires) for i in left + right)
            wires.append(all(wires[i] for i in left) or all(wires[i] for i in right))
        output = program['output_conjunction']
        assert all(0 <= i < len(wires) for i in output)
        assert all(wires[i] for i in output) == any((x >> a & 1) and (x >> b & 1) for a, b in EDGES)
    print('Five-OR circuit verified on all 64 assignments.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run Python without -O so every certificate check is enabled.')
    replay()
    witness()
