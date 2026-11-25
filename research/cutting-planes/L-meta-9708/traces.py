"""Replay two concrete cutting-planes refutations for six pigeons and five holes."""
from collections import Counter
from itertools import combinations


def refutation(shallow):
    steps = []

    def emit(*instruction):
        steps.append(instruction)
        return len(steps) - 1

    def add_all(indices):
        result = indices[0]
        for other in indices[1:]:
            result = emit("add", result, other)
        return result

    capacities = []
    for hole in range(5):
        if shallow:
            pairs = {(i, j): emit("pair", hole, i, j)
                     for i, j in combinations(range(6), 2)}

            def triangle(pigeons):
                sides = [pairs[i, j] for i, j in combinations(pigeons, 2)]
                return emit("div", add_all(sides), 2)

            first = triangle((0, 1, 2))
            others = [triangle((i, 3, 4)) for i in range(3)]
            scaled = emit("mul", first, 2)
            five = emit("div", add_all([scaled, *others]), 3)
            base = emit("mul", five, 4)
            cap = emit("div", add_all([base, *(pairs[i, 5] for i in range(5))]), 5)
        else:
            cap = emit("pair", hole, 0, 1)
            for k in range(2, 6):
                spokes = [emit("pair", hole, i, k) for i in range(k)]
                weighted = cap if k == 2 else emit("mul", cap, k - 1)
                cap = emit("div", add_all([weighted, *spokes]), k)
        capacities.append(cap)
    add_all(capacities + [emit("pigeon", i) for i in range(6)])
    return steps


def replay(steps):
    """Represent each line as a·x ≥ b and count divisions on its longest path."""
    lines = []
    depths = []
    for op, *args in steps:
        a = [0] * 30
        depth = 0
        if op == "pigeon":
            (p,) = args
            assert 0 <= p < 6
            for h in range(5):
                a[5*p + h] = 1
            b = 1
        elif op == "pair":
            h, p, q = args
            assert 0 <= p < q < 6 and 0 <= h < 5
            a[5*p + h] = a[5*q + h] = -1
            b = -1
        elif op == "add":
            i, j = args
            assert 0 <= i < len(lines) and 0 <= j < len(lines)
            a = [x+y for x, y in zip(lines[i][0], lines[j][0])]
            b = lines[i][1] + lines[j][1]
            depth = max(depths[i], depths[j])
        elif op in ("mul", "div"):
            i, k = args
            assert 0 <= i < len(lines) and k > 0
            coeffs, rhs = lines[i]
            if op == "mul":
                a, b = [k*x for x in coeffs], k*rhs
                depth = depths[i]
            else:
                assert all(x % k == 0 for x in coeffs)
                a, b = [x // k for x in coeffs], -((-rhs) // k)
                depth = depths[i] + 1
        else:
            raise ValueError(op)
        lines.append((a, b))
        depths.append(depth)
    assert lines[-1] == ([0]*30, 1)
    return len(steps), depths[-1], dict(sorted(Counter(s[0] for s in steps).items()))


if __name__ == "__main__":
    for shallow, expected in [(False, (196, 4)), (True, (211, 3))]:
        count, depth, histogram = replay(refutation(shallow))
        assert (count, depth) == expected
        print(f"{count} lines, division depth {depth}, instructions {histogram}")
