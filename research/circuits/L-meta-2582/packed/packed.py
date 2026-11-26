"""Compare a 9-bit read-2 checker with cap-3 joint vectors on finite planes."""
from dataclasses import dataclass, field
from functools import cache
from itertools import combinations, product


def pair_bit(a, b):
    return 1 << (3 * a + b)


# The mask prevents row wrap and removes overflowing columns before each shift.
TRANSLATABLE = [
    sum(pair_bit(c, d) for c in range(3 - a) for d in range(3 - b))
    for a, b in product(range(3), repeat=2)
]


@cache
def packed_and(left, right):
    accumulated = 0
    while left:
        bit = left & -left
        offset = bit.bit_length() - 1
        accumulated |= (right & TRANSLATABLE[offset]) << offset
        left ^= bit
    return accumulated


@cache
def capped_and(left, right):
    return frozenset((min(3, a + c), min(3, b + d))
                     for a, b in left for c, d in right)


@cache
def project(pairs):
    return sum(pair_bit(a, b) for a, b in pairs if a <= 2 and b <= 2)


def field_mul(q, a, b):
    if q in (2, 3):
        return a * b % q
    assert q == 4
    # GF(4) = GF(2)[t]/(t^2+t+1), with binary polynomial coefficients.
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 0b111
    return result


def incident(q, point, line):
    products = [field_mul(q, a, b) for a, b in zip(point, line)]
    if q == 4:
        return products[0] ^ products[1] ^ products[2] == 0
    return sum(products) % q == 0


def plane(q):
    # Nonzero representatives scaled so their first nonzero coordinate is one.
    vectors = [v for v in product(range(q), repeat=3)
               if next((x for x in v if x), 0) == 1]
    rows = [set(j for j, line in enumerate(vectors) if incident(q, point, line))
            for point in vectors]
    n = q * q + q + 1
    assert len(rows) == n and all(len(row) == q + 1 for row in rows)
    columns = [{i for i, row in enumerate(rows) if j in row} for j in range(n)]
    assert all(len(col) == q + 1 for col in columns)
    assert all(len(a & b) == 1 for a, b in combinations(rows, 2))
    assert all(len(a & b) == 1 for a, b in combinations(columns, 2))
    return rows


@dataclass
class Circuit:
    inputs: int
    gates: list = field(default_factory=list)

    def append(self, op, a, b):
        wire = self.inputs + len(self.gates)
        assert op in ('and', 'or') and 0 <= a < wire and 0 <= b < wire
        self.gates.append((op, a, b))
        return wire

    def fold_or(self, wires):
        first, *rest = wires
        for wire in rest:
            first = self.append('or', first, wire)
        return first


def make_circuit(rows):
    n = len(rows)
    circuit = Circuit(2 * n)
    stars = []
    for point, row in enumerate(rows):
        line_sum = circuit.fold_or([n + j for j in sorted(row)])
        stars.append(circuit.append('and', point, line_sum))
    normal = circuit.fold_or(stars)
    original_size = len(circuit.gates)
    any_input = circuit.fold_or(list(range(circuit.inputs)))
    extension = circuit.append('and', normal, any_input)
    inflated = circuit.append('and', normal, extension)
    return circuit, normal, inflated, original_size


def verify_pair(circuit, point, line, normal, inflated, is_edge):
    packed = [0] * circuit.inputs
    packed[point], packed[line] = pair_bit(1, 0), pair_bit(0, 1)
    empty = frozenset()
    capped = [empty] * circuit.inputs
    capped[point], capped[line] = frozenset([(1, 0)]), frozenset([(0, 1)])
    for i, (op, a, b) in enumerate(circuit.gates):
        if op == 'or':
            packed.append(packed[a] | packed[b])
            capped.append(capped[a] | capped[b])
        else:
            packed.append(packed_and(packed[a], packed[b]))
            capped.append(capped_and(capped[a], capped[b]))
        assert packed[-1] == project(capped[-1]), (point, line, i)
    if is_edge:
        assert capped[normal] == {(1, 1)}
        assert capped[inflated] == {(2, 3), (3, 2)}
        assert packed[normal] == pair_bit(1, 1) and packed[inflated] == 0
    else:
        assert not capped[normal] and not capped[inflated]
    return (bool(packed[normal]), bool(packed[inflated]),
            all(any(pair[i] <= 2 for pair in capped[inflated]) for i in (0, 1)))


def exhaustive_fano(circuit, normal, inflated, rows):
    count = 1 << circuit.inputs
    # Evaluate all assignments together, using a single Boolean bit per assignment.
    all_assignments = (1 << count) - 1
    wires = []
    for i in range(circuit.inputs):
        block_width = 1 << i
        pattern = (all_assignments // ((1 << block_width) + 1)) << block_width
        wires.append(pattern)
    for op, a, b in circuit.gates:
        wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    # Independently evaluate the defining incidence predicate assignment by assignment.
    n = len(rows)
    incidence_masks = [sum(1 << j for j in row) for row in rows]
    expected = bytearray((count + 7) // 8)
    for assignment in range(count):
        lines = assignment >> n
        if any((assignment >> i & 1) and lines & incident_lines
               for i, incident_lines in enumerate(incidence_masks)):
            expected[assignment // 8] |= 1 << (assignment % 8)
    truth = int.from_bytes(expected, 'little')
    assert wires[normal] == truth == wires[inflated]
    return count, truth.bit_count()


def check_packed_algebra():
    cells = list(product(range(3), repeat=2))
    members = [[pair for i, pair in enumerate(cells) if (mask >> i) & 1]
               for mask in range(512)]
    for left, left_pairs in enumerate(members):
        for right, right_pairs in enumerate(members):
            expected = 0
            for a, b in left_pairs:
                for c, d in right_pairs:
                    if a + c <= 2 and b + d <= 2:
                        expected |= pair_bit(a + c, b + d)
            assert packed_and(left, right) == expected, (left, right)
    packed_and.cache_clear()
    return len(members) ** 2


def main():
    print('ordered 9-bit AND table entries verified', check_packed_algebra())
    print('q | points | all point-line pairs | edges | star gates | inflated gates | '
          'star joint-pass | inflated joint-pass | inflated scalar-pass | gate comparisons')
    for order in (2, 3, 4):
        rows = plane(order)
        n = len(rows)
        circuit, normal, inflated, star_size = make_circuit(rows)
        assert star_size == n * (order + 2) - 1
        assert len(circuit.gates) == star_size + 2 * n + 1
        totals = [0, 0, 0]
        for p, row in enumerate(rows):
            for l in range(n):
                result = verify_pair(circuit, p, n + l, normal, inflated, l in row)
                for i, value in enumerate(result):
                    totals[i] += value
        edges = sum(map(len, rows))
        assert totals == [edges, 0, edges]
        print(order, n, n**2, edges, star_size, len(circuit.gates), *totals,
              n**2 * len(circuit.gates))
        if order == 2:
            assignments, positives = exhaustive_fano(circuit, normal, inflated, rows)
            print('Fano truth-table assignments', assignments, 'true', positives,
                  'false', assignments - positives)


if __name__ == '__main__':
    main()
