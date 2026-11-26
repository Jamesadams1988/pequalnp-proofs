"""Exhaust compatibility classes for factors formed by coalescing complete rows."""
from itertools import combinations, product

N = 13
POINTS = tuple(range(N))
GRAPH = frozenset((p, l) for p, l in product(POINTS, repeat=2)
                  if (p + l) % N in (0, 1, 3, 9))
NONEDGES = frozenset(product(POINTS, repeat=2)) - GRAPH
ROWS = [{l for i, l in GRAPH if i == p} for p in POINTS]
COLUMNS = [{p for p, j in GRAPH if j == l} for l in POINTS]


def partitions(elements):
    if not elements:
        yield []
        return
    first, *rest = elements
    for blocks in partitions(rest):
        yield [[first]] + blocks
        for i in range(len(blocks)):
            yield blocks[:i] + [[first] + blocks[i]] + blocks[i + 1:]


def extra_edges(blocks):
    enlarged = set()
    for block in blocks:
        lines = set.union(*(ROWS[p] for p in block))
        enlarged.update(product(block, lines))
    return frozenset(enlarged - GRAPH)


def compatible_with_all(extras):
    return {b for b in NONEDGES if all(
        (a[0], b[1]) in GRAPH or (b[0], a[1]) in GRAPH for a in extras)}


def census():
    first_factors = set()
    for p,q in combinations(POINTS, 2):
        common, = ROWS[p] & ROWS[q]
        allowed = compatible_with_all(extra_edges([[p, q]]))
        assert allowed == {(s, common) for s in POINTS if s not in COLUMNS[common]}
    for line, points in enumerate(COLUMNS):
        for blocks in partitions(sorted(points)):
            extras = extra_edges(blocks)
            if not extras:
                continue
            possible = compatible_with_all(extras)
            assert possible == {(s, line) for s in POINTS if s not in points}
            assert len(possible) == 9 and extras not in first_factors
            first_factors.add(extras)
    assert len(first_factors) == 182
    print('row pairs', N * (N-1) // 2, 'first factors', len(first_factors),
          'strict ordered pairs', len(first_factors) * (2**9 - 1))


def example():
    gates = []
    def gate(op, a, b):
        wire = 2*N + len(gates)
        assert 0 <= a < wire and 0 <= b < wire
        gates.append((op, a, b))
        return wire
    def fold_or(wires):
        first, *rest = wires
        for w in rest:
            first = gate('or', first, w)
        return first
    p, q = 0, 1
    line, = ROWS[p] & ROWS[q]
    s = min(set(POINTS) - COLUMNS[line])
    sums = [fold_or([N+l for l in sorted(row)]) for row in ROWS]
    common = fold_or([gate('and', i, sums[i]) for i in POINTS if i not in (p,q)])
    grouped = gate('and', gate('or', p, q), gate('or', sums[p], sums[q]))
    first = gate('or', common, grouped)
    second = fold_or([common, gate('and', p, sums[p]), gate('and', q, sums[q]),
                      gate('and', s, N+line)])
    factors = [set(),set()]
    for i, j in product(POINTS, repeat=2):
        inputs = [k == i or k == N+j for k in range(2*N)]
        for op,a,b in gates:
            inputs.append(inputs[a] and inputs[b] if op=='and' else inputs[a] or inputs[b])
        for factor,output in zip(factors,[first,second]):
            if inputs[output]:
                factor.add((i,j))
    wanted = [GRAPH | extra_edges([[p,q]]), GRAPH | {(s,line)}]
    assert factors == wanted
    assert compatible_with_all(factors[0] - GRAPH) >= factors[1] - GRAPH
    assert len(gates) == 70
    print('example gates', len(gates), 'factor edge counts', *(len(f) for f in factors),
          'merged rows',p,q,'second extra',s,line)


if __name__ == '__main__':
    census()
    example()
