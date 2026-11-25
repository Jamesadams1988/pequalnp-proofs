"""Check a PG(2,4) monotone circuit against every minimal true and maximal false input.

A JSON circuit has "gates" and "output". Each gate is ["and" or "or", [input indices]].
Indices 0..41 are the primary inputs. Gates append one wire at a time. The format
also accepts zero or one operand. A wire absent at evaluation time defaults to false.
Without a filename this program checks the 104-OR star construction.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

ORDER = 21
FULL = (1 << ORDER) - 1
OFFSETS = (0, 5, 7, 17, 20)
LOW_BITS = ORDER // 2
LOW_MASK = (1 << LOW_BITS) - 1


def incidence_rows():
    return [sum(1 << ((p + d) % ORDER) for d in OFFSETS) for p in range(ORDER)]


def union_table(rows):
    table = [0]
    for row in rows:
        table.extend(item | row for item in table[:])
    return table


def union_lookup(rows):
    low, high = union_table(rows[:LOW_BITS]), union_table(rows[LOW_BITS:])

    def lookup(bits):
        return low[bits & LOW_MASK] | high[bits >> LOW_BITS]
    return lookup


def maximal_false(rows):
    incident_lines = union_lookup(rows)
    columns = [sum(1 << p for p, row in enumerate(rows) if row >> h & 1)
               for h in range(ORDER)]
    incident_points = union_lookup(columns)
    for points in range(1 << ORDER):
        lines = FULL ^ incident_lines(points)
        if points == FULL ^ incident_points(lines):
            yield points | (lines << ORDER)


def test_inputs():
    rows = incidence_rows()
    edges = [(1 << p) | (1 << (ORDER + h)) for p, row in enumerate(rows)
             for h in range(ORDER) if row >> h & 1]
    return edges, list(maximal_false(rows))


def star_circuit():
    gates = []
    def emit(op, a, b):
        wire = 2 * ORDER + len(gates)
        gates.append([op, [a, b]])
        return wire
    def disjoin(wires):
        first, *rest = wires
        for other in rest:
            first = emit('or', first, other)
        return first
    stars = []
    for p, row in enumerate(incidence_rows()):
        line_wires = [ORDER + h for h in range(ORDER) if row >> h & 1]
        stars.append(emit('and', p, disjoin(line_wires)))
    return {'gates': gates, 'output': disjoin(stars)}


class ExtremalTests:
    def __init__(self):
        edges, independent = test_inputs()
        self.examples = edges + independent
        self.positive = (1 << len(edges)) - 1
        self.all = (1 << len(self.examples)) - 1
        self.edge_count = len(edges)
        self.false_count = len(independent)
        self.independent_sizes = Counter(s.bit_count() for s in independent)
        packed = [bytearray((len(self.examples) + 7) // 8) for _ in range(2 * ORDER)]
        for i, support in enumerate(self.examples):
            while support:
                bit = support & -support
                packed[bit.bit_length() - 1][i // 8] |= 1 << (i % 8)
                support ^= bit
        self.inputs = [int.from_bytes(column, 'little') for column in packed]

    def check(self, circuit):
        gates, output = circuit['gates'], circuit['output']
        if not isinstance(gates, list) or type(output) is not int or output < 0:
            raise ValueError('Expected a gate list and a natural-number output wire.')
        wires = self.inputs.copy()
        counts = Counter()

        def wire(index):
            if type(index) is not int or index < 0:
                raise ValueError('Wire indices must be natural numbers.')
            return wires[index] if index < len(wires) else 0

        for op, indices in gates:
            if op not in ('and', 'or') or not isinstance(indices, list) or len(indices) > 2:
                raise ValueError('Expected AND or OR with at most two operands.')
            value = self.all if op == 'and' else 0
            for index in indices:
                operand = wire(index)
                value = value & operand if op == 'and' else value | operand
            wires.append(value)
            counts[op] += 1
        observed = wire(output)
        difference = observed ^ self.positive
        result = {'correct': difference == 0, 'or_gates': counts['or'], 'and_gates': counts['and'],
                  'matches_103_or_budget': counts['or'] <= 103}
        if difference:
            index = (difference & -difference).bit_length() - 1
            case = self.examples[index]
            result['counterexample'] = {
                'points': [p for p in range(ORDER) if case >> p & 1],
                'lines': [h for h in range(ORDER) if case >> (h + ORDER) & 1],
                'expected': index < self.edge_count,
                'observed': bool(observed >> index & 1)}
        return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('circuit', nargs='?', type=Path)
    args = parser.parse_args()
    tests = ExtremalTests()
    candidate = json.loads(args.circuit.read_bytes()) if args.circuit else star_circuit()
    result = tests.check(candidate)
    result['minimal_true_inputs'] = tests.edge_count
    result['maximal_false_inputs'] = tests.false_count
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['correct'] else 1)
