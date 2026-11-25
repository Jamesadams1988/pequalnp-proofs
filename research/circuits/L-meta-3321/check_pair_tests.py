"""Check a ten-gate circuit for the perfect matching on three points and lines.

Input masks use p0, p1, p2, l0, l1, l2 from least to most significant bit.
Gate numbers start at zero; their wire numbers start at six.
"""

GATES = (
    ('or', 5, 1), ('and', 4, 6), ('or', 3, 7), ('and', 0, 8),
    ('or', 3, 2), ('and', 9, 10), ('and', 1, 7), ('and', 2, 5),
    ('or', 11, 12), ('or', 14, 13),
)


def wires(mask, force=None):
    values = [bool(mask >> i & 1) for i in range(6)]
    for i, (op, a, b) in enumerate(GATES):
        assert 0 <= a < len(values) and 0 <= b < len(values)
        value = values[a] and values[b] if op == 'and' else values[a] or values[b]
        values.append(force[1] if force is not None and force[0] == i else value)
    return values


def matched(mask):
    return bool((mask & 7) & (mask >> 3))


def main():
    rows = range(64)
    assert all(wires(m)[-1] == matched(m) for m in rows)
    input_masks = [1 << i for i in range(6)]
    input_masks += [(1 << p) | (1 << (3 + line))
                    for p in range(3) for line in range(3) if p != line]
    ands = [6 + j for j, (op, _, _) in enumerate(GATES) if op == 'and']
    assert all(not wires(m)[w] for m in input_masks for w in ands)
    bad = [m for m in rows if not matched(m) and wires(m)[9]
           and not wires(m & 7)[9] and not wires(m & 56)[9]]
    assert 49 in bad and min(m.bit_count() for m in bad) == 3
    reached = {15}
    for j in reversed(range(len(GATES))):
        if 6 + j in reached:
            reached.update(GATES[j][1:])
    assert reached == set(range(16))
    print('All 64 assignments match the 3-edge perfect matching.')
    print('All 5 AND gates pass all 6 singleton and 6 nonincident mixed-pair tests.')
    print('Wire 9 fails the clean clause first at size 3; mask 49 has pure masks 1 and 48.')
    print('All 10 gates and 6 inputs have a path to the output.')
    print('Gate  Wire  Forced 0 witness  Forced 1 witness')
    for j in range(len(GATES)):
        witnesses = []
        for value in [False, True]:
            changed = [m for m in rows if wires(m, (j, value))[-1] != matched(m)]
            assert changed, (j, value)
            witnesses.append(min(changed, key=lambda m: (m.bit_count(), m)))
        print(f'{j:4} {6+j:5} {witnesses[0]:17} {witnesses[1]:17}')


if __name__ == '__main__':
    main()
