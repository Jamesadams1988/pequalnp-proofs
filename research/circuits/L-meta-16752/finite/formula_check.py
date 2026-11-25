"""Exact formula leaf bounds via disjoint partitions of labeled row sets.

Bit i of a row is input i. For any positive/negative sample, an OR gate
partitions positive rows between its children and an AND gate partitions
negative rows. Conversely such a partition combines two separators.
The root optimum is thus a lower bound for formulas correct on all rows.
An explicit witness attaining this bound is checked on every complete row.
"""
from functools import cache

TARGET = (4276809450 << 32) + 4276808362
CORE = 0xE8A8E880


def boundary(table, n):
    rows = range(1 << n)
    positive = [r for r in rows if (table >> r) & 1]
    negative = [r for r in rows if not ((table >> r) & 1)]
    return ([r for r in positive if not any(s != r and s & r == s for s in positive)],
            [r for r in negative if not any(s != r and s | r == s for s in negative)])


def splits(bits):
    """One ordering per unordered, nontrivial bipartition."""
    small = bits & -bits
    sub = (bits - 1) & bits
    while sub:
        if sub & small:
            yield sub, bits ^ sub
        sub = (sub - 1) & bits


def solve(positive, negative, n, signed):
    options = []
    for i in range(n):
        for sign in ([1, 0] if signed else [1]):
            p = sum(int(((r >> i) & 1) == sign) << j for j, r in enumerate(positive))
            q = sum(int(((r >> i) & 1) != sign) << j for j, r in enumerate(negative))
            options.append((p, q, (i, sign)))

    @cache
    def optimum(p, q):
        for pp, qq, leaf in options:
            if not (p & ~pp or q & ~qq):
                return 1, leaf
        best, tree = 1 << 30, None
        for op, label in (('|', p), ('&', q)):
            for a, b in splits(label):
                lhs, rhs = ((a, q), (b, q)) if op == '|' else ((p, a), (p, b))
                ls, lt = optimum(*lhs)
                if ls + 1 >= best:
                    continue
                rs, rt = optimum(*rhs)
                if ls + rs < best:
                    best, tree = ls + rs, (op, lt, rt)
        return best, tree

    return optimum((1 << len(positive)) - 1, (1 << len(negative)) - 1)


def evaluate(tree, row):
    if len(tree) == 2:
        i, sign = tree
        return ((row >> i) & 1) == sign
    op, lhs, rhs = tree
    left, right = evaluate(lhs, row), evaluate(rhs, row)
    return (left and right) if op == '&' else (left or right)


def display(tree):
    if len(tree) == 2:
        return ('x' if tree[1] else '!x') + str(tree[0])
    return '(' + display(tree[1]) + ' ' + tree[0] + ' ' + display(tree[2]) + ')'


def table_of(tree, n):
    return sum(int(evaluate(tree, row)) << row for row in range(1 << n))


def main():
    assert all(((TARGET >> r) & 1) == ((r & 1) or ((CORE >> (r >> 1)) & 1)) for r in range(64))
    for n, table in ((5, CORE), (6, TARGET)):
        p, q = boundary(table, n)
        stride = 1 if n == 5 else 2
        p.extend([27 * stride, 30 * stride])
        q.extend([8 * stride, 6 * stride])
        assert len(set(p)) == len(p) and len(set(q)) == len(q)
        assert all(table >> r & 1 for r in p) and all(not (table >> r & 1) for r in q)
        print(f'{n} inputs 0x{table:x}; positive sample {p}; negative sample {q}')
        for signed in (False, True):
            size, tree = solve(p, q, n, signed)
            assert size == n + 4 and table_of(tree, n) == table
            print(f'{"De Morgan" if signed else "monotone"} formula minimum {size} leaves; '
                  f'checked all {1 << n} rows; {display(tree)}')


if __name__ == '__main__':
    main()
