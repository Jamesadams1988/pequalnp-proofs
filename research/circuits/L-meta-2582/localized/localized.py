"""One inflated Fano point-star; check every truth assignment and point-line pair."""
from itertools import product
from pathlib import Path
import sys

N = 7
ROWS = [[l for l in range(N) if ((p + 1) & (l + 1)).bit_count() % 2 == 0]
        for p in range(N)]
assert all(len(row) == 3 for row in ROWS)


def build(marked=None):
    gates = []

    def gate(op, a, b):
        out = 2 * N + len(gates)
        assert op in ('and', 'or') and 0 <= a < out and 0 <= b < out
        gates.append((op, a, b))
        return out

    def fold_or(wires):
        first, *rest = wires
        for w in rest:
            first = gate('or', first, w)
        return first

    stars = []
    for p, row in enumerate(ROWS):
        lines = fold_or([N + l for l in row])
        active = gate('and', p, lines)
        if p == marked:
            either = gate('or', p, lines)
            both = gate('and', active, either)
            active = gate('and', active, both)
        stars.append(active)
    return gates, fold_or(stars)


def parse_counts(gates, output, p, l):
    wires = [set() for _ in range(2 * N)]
    wires[p] = {(1, 0)}
    wires[N + l] = {(0, 1)}
    for op, a, b in gates:
        if op == 'or':
            result = wires[a] | wires[b]
        else:
            result = {(x + s, y + t) for (x, y), (s, t) in product(wires[a], wires[b])}
        wires.append(result)
    return wires[output]


def fano_truth(gates, out):
    cases = 1 << (2 * N)
    all_ones = (1 << cases) - 1
    wires = []
    for i in range(2 * N):
        run = 1 << i
        wires.append((all_ones // ((1 << run) + 1)) << run)
    for op, a, b in gates:
        wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    return wires[out]


def lean_source(original, localized):
    def declaration(name, program):
        gates, out = program
        body = ',\n  '.join(f'⟨.{op}, [{a}, {b}]⟩' for op, a, b in gates)
        return f'def {name} : Circuit := ⟨[{body}], {out}⟩\n'

    lines = ['import PEqualNP.Defs', '', 'namespace LocalizedFanoStar',
             'open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK', '',
             'set_option maxRecDepth 32000', 'set_option maxHeartbeats 4000000', '',
             declaration('original', original), declaration('localized', localized),
             'theorem model : TopForm.IsAO2 14 original ∧ TopForm.IsAO2 14 localized ∧',
             '    original.size = 27 ∧ localized.size = 30 := by decide', '',
             'theorem localBoolean (x y : Bool) :',
             '    ((x && y) && ((x && y) && (x || y))) = (x && y) := by cases x <;> cases y <;> rfl', '']
    for p, row in enumerate(ROWS):
        for l in row:
            s = f'[{p}, {N + l}]'
            expected = 'false' if p == 0 else 'true'
            lines.extend([f'theorem edge_{p}_{l} :',
                          f'    readsAtMost original 14 {s} 2 = true ∧',
                          f'    eachReadsAtMost localized 14 {s} 2 = true ∧',
                          f'    readsAtMost localized 14 {s} 2 = {expected} := by decide'])
    lines.extend(['', '#print axioms model', '#print axioms edge_0_1',
                  '#print axioms edge_1_0', '', 'end LocalizedFanoStar'])
    return '\n'.join(lines) + '\n'


def main():
    original = build()
    localized = build(0)
    assert len(original[0]) == 27 and len(localized[0]) == 30
    normal = fano_truth(*original)
    altered = fano_truth(*localized)
    assert normal == altered
    masks = [sum(1 << l for l in row) for row in ROWS]
    for z in range(1 << (2 * N)):
        target = any(((z >> p) & 1) and (masks[p] & (z >> N)) for p in range(N))
        assert bool((altered >> z) & 1) == target
    counts = {'edge': 0, 'scalar': 0, 'joint': 0, 'nonedge': 0}
    failed = []
    for p, l in product(range(N), repeat=2):
        before = parse_counts(*original, p, l)
        after = parse_counts(*localized, p, l)
        if l not in ROWS[p]:
            assert before == after == set()
            counts['nonedge'] += 1
            continue
        assert before == {(1, 1)}
        assert after == ({(2, 3), (3, 2)} if p == 0 else {(1, 1)})
        counts['edge'] += 1
        counts['scalar'] += all(min(pair[i] for pair in after) <= 2 for i in (0, 1))
        good = any(max(pair) <= 2 for pair in after)
        counts['joint'] += good
        if not good:
            failed.append((p, l))
    assert counts == {'edge': 21, 'scalar': 21, 'joint': 18, 'nonedge': 28}
    print('gates', len(original[0]), len(localized[0]))
    print('assignments', 1 << (2 * N), 'true', altered.bit_count(), 'false',
          (1 << (2 * N)) - altered.bit_count())
    print(counts)
    print('failed (point index, line index)', failed)
    source = Path(__file__).with_name('LocalizedFano.lean')
    if sys.argv[1:] == ['--emit-lean']:
        source.write_text(lean_source(original, localized))
    else:
        assert source.read_text() == lean_source(original, localized)


if __name__ == '__main__':
    main()
