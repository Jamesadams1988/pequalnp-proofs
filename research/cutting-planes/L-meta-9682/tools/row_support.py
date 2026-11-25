"""Construct a half-integral feasible assignment for a signed PHP objective.

For each row select its top three coefficients. The returned assignment has
each row sum one and every pair of entries in a column sums to at most one.
Its objective reaches the ceiling of one third of the sum of the selected
coefficients. Rows are pigeons, columns are holes. Use integer coefficients.
"""
from itertools import combinations


def support_witness(rows):
    if not rows or len(rows[0]) < 3 or any(len(r) != len(rows[0]) for r in rows):
        raise ValueError('expected a nonempty rectangular array with at least three columns')
    if any(type(value) is not int for row in rows for value in row):
        raise ValueError('expected integer coefficients')

    n = len(rows[0])
    top = [sorted(range(n), key=lambda j: (-row[j], j))[:3] for row in rows]
    minima = [row[j[2]] for row, j in zip(rows, top)]
    mass = sum(row[j] - low for row, chosen, low in zip(rows, top, minima)
               for j in chosen)
    doubled = [[0] * n for _ in rows]
    if mass == 1:
        # The sole positive residual coefficient can collect a whole unit.
        i = next(i for i, js in enumerate(top) if rows[i][js[0]] > minima[i])
        occupied = top[i][0]
        doubled[i][occupied] = 2
        for h, js in enumerate(top):
            if h != i:
                a, b = [j for j in js if j != occupied][:2]
                doubled[h][a] = doubled[h][b] = 1
    else:
        # Giving one half to each of the top two collects exactly mass / 2
        # above the integer baseline. For mass != 1 this reaches ceil(mass/3).
        for half_row, (a, b, _) in zip(doubled, top):
            half_row[a] = half_row[b] = 1

    top_sum = sum(row[j] for row, js in zip(rows, top) for j in js)
    ceiling = -((-top_sum) // 3)
    doubled_value = sum(a*x for row, point in zip(rows, doubled) for a, x in zip(row, point))
    if doubled_value < 2*ceiling:
        raise ArithmeticError('constructed objective is below the required ceiling')
    return doubled, ceiling


def verify(rows, point, ceiling):
    n = len(rows[0])
    assert len(rows) == len(point) and all(len(p) == n for p in point)
    assert all(sum(p) == 2 and all(v in (0, 1, 2) for v in p) for p in point)
    assert all(p[j] + q[j] <= 2 for p, q in combinations(point, 2) for j in range(n))
    assert sum(sum(a*b for a,b in zip(row,p)) for row,p in zip(rows,point)) >= 2*ceiling
    # Independent objective calculation without sorting or choosing tie-breaks.
    best = sum(max(sum(three) for three in combinations(row, 3)) for row in rows)
    assert ceiling == (best+2)//3


if __name__ == '__main__':
    from itertools import product
    import random
    controls = 0
    for values in product((-1, 0, 1), repeat=9):
        objective = [values[i:i+3] for i in range(0, 9, 3)]
        verify(objective, *support_witness(objective))
        controls += 1
    rng = random.Random(9682)
    for m in (1, 3, 4, 6, 9):
        for n in range(3, 9):
            for _ in range(100):
                rows = [[rng.randint(-50, 50) for _ in range(n)] for _ in range(m)]
                verify(rows, *support_witness(rows))
                controls += 1
    # In this example the high entry lies in column zero. In other rows
    # column zero is tied for third place or does not belong to the top three.
    rows = [[2,1,1,-10,-20],[0,0,0,-5,-5],[-5,0,0,0,-10]]
    verify(rows, *support_witness(rows))
    print(controls+1, 'objective and complete feasibility checks passed')
