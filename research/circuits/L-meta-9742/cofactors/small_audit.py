"""Check the cofactor recurrence and exact small monotone DAG sizes."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


# Five-variable truth tables use one Python integer per wire. A graph with fewer
# inputs is embedded by leaving its extra variables unused.
INPUTS = tuple(sum(1 << mask for mask in range(32) if mask >> v & 1) for v in range(5))
PAIRS = tuple(product(range(2), range(2, 5)))


def truth_table(edges):
    value = 0
    for a, b in edges:
        value |= INPUTS[a] & INPUTS[b]
    return value


def exact_sizes():
    targets = {truth_table([e for j, e in enumerate(PAIRS) if mask >> j & 1])
               for mask in range(1 << len(PAIRS))}
    sizes = {0: 0}
    states = {()}
    for depth in range(1, 6):
        next_states = set()
        for state in states:
            wires = INPUTS + state
            present = set(wires)
            for a, b in combinations(wires, 2):
                for value in (a & b, a | b):
                    if value in present:
                        continue
                    if value in targets:
                        sizes.setdefault(value, depth)
                        if len(sizes) == len(targets):
                            return sizes
                    if depth < 5:
                        next_states.add(tuple(sorted((*state, value))))
        states = next_states
    raise AssertionError("five gates did not reach every 2-by-3 graph")


def reference(edges, n):
    """Use actual immutable edge sets, removing isolates implicitly."""
    @lru_cache(None)
    def visit(es):
        if not es:
            return 0, (0, 0, 0)
        vertices = {v for edge in es for v in edge}
        if len(vertices) == 2:
            return 1, (0, 0, 0)
        scores = {}
        base = len(vertices) - 1
        for v in vertices:
            neighbors = {w for edge in es if v in edge for w in edge if w != v}
            low_edges = frozenset(edge for edge in es if v not in edge)
            high_edges = frozenset(edge for edge in low_edges if not neighbors.intersection(edge))
            low = visit(low_edges)[0]
            high = len(neighbors) + (visit(high_edges)[0] if high_edges else -1)
            scores[v] = (max(low + 2, high + 1), max(low + 1, high + 2))
            base = max(base, 1 + low, 1 + high)
        # Enumerate each potential first pair. This checks the optimized second
        # order statistic, including ties, without reproducing its implementation.
        and_floor, or_floor = (
            min(max(scores[u][op], scores[v][op]) for u, v in combinations(vertices, 2))
            for op in (0, 1)
        )
        return max(base, min(and_floor, or_floor)), (base, and_floor, or_floor)

    es = frozenset(edges)
    vertices = range(n)
    core_count = 0
    for mask in range(1, 1 << n):
        chosen = {v for v in vertices if mask >> v & 1}
        induced = [e for e in es if set(e) <= chosen]
        if {v for edge in induced for v in edge} == chosen:
            core_count += 1
    expected, floors = visit(es)
    has_floors = n > 2 and {v for edge in es for v in edge} == set(vertices)
    return expected, core_count, floors if has_floors else None


def compare(solver, p, q, edges):
    expected, cores, floors = reference(edges, p + q)
    data = f"{p} {q} {len(edges)}\n" + "".join(f"{u} {v}\n" for u, v in edges)
    result = subprocess.run([solver], input=data, text=True, capture_output=True, check=True)
    summary = re.search(r"masks (\d+); nonempty isolate-free masks (\d+); "
                        r"monotone size lower bound (\d+)\n$", result.stdout)
    if not summary or tuple(map(int, summary.groups())) != (1 << (p + q), cores, expected):
        raise AssertionError((p, q, edges, expected, cores, result.stdout))
    split = re.search(r"root general-pin floor (\d+); first-AND floor (\d+); "
                      r"first-OR floor (\d+)", result.stdout)
    observed = tuple(map(int, split.groups())) if split else None
    if observed != floors:
        raise AssertionError((p, q, edges, observed, floors))
    return expected


def audit(solver):
    sizes = exact_sizes()
    histogram = Counter()
    total = 0
    for p in range(1, 3):
        for q in range(1, 4):
            pairs = tuple(product(range(p), range(p, p + q)))
            for mask in range(1 << len(pairs)):
                edges = [edge for i, edge in enumerate(pairs) if mask >> i & 1]
                lower = compare(solver, p, q, edges)
                embedded = [(u, 2 + v - p) for u, v in edges]
                exact = sizes[truth_table(embedded)]
                if lower > exact:
                    raise AssertionError((p, q, edges, lower, exact))
                histogram[exact - lower] += 1
                total += 1
    print(f"{total} labeled graphs through 2 by 3 matched the reference recurrence.")
    print(f"Exact 2-by-3 sizes: {dict(sorted(Counter(sizes.values()).items()))}")
    print(f"Exact size minus reported lower bound across all {total}: {dict(sorted(histogram.items()))}")


def full_core_audit(solver):
    # Fix the left subset A. Its right subset must lie in N(A) and intersect
    # every row of A. Inclusion-exclusion counts these in 3^p total terms.
    data = subprocess.check_output([sys.executable, "-B",
                                    str(Path(__file__).with_name("extract.py"))], text=True)
    heading, *lines = data.splitlines()
    p, q, _ = map(int, heading.split())
    neighbors = [0] * p
    for line in lines:
        a, b = map(int, line.split())
        neighbors[a] |= 1 << (b - p)
    unions = [0] * (1 << p)
    for a in range(1, 1 << p):
        bit = a & -a
        unions[a] = unions[a ^ bit] | neighbors[bit.bit_length() - 1]
    count = 0
    for a in range(1, 1 << p):
        sub = a
        while True:
            choices = 1 << (unions[a] & ~unions[sub]).bit_count()
            count += -choices if sub.bit_count() % 2 else choices
            if not sub:
                break
            sub = (sub - 1) & a
    result = subprocess.run([solver], input=data, text=True, capture_output=True, check=True)
    expected = (f"root general-pin floor 29; first-AND floor 29; first-OR floor 29\n"
                f"masks {1 << (p + q)}; nonempty isolate-free masks {count}; "
                f"monotone size lower bound 29\n")
    if count != 30_185_957 or result.stdout != expected:
        raise AssertionError((count, result.stdout))
    print(f"Independent inclusion-exclusion counted {count:,} nonempty isolate-free masks.")
    print("The assigned graph reproduced the three reported root floors of 29.")


def run(solver, full):
    audit(solver)
    if full:
        full_core_audit(solver)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, help="use an existing bound.cpp executable")
    parser.add_argument("--full", action="store_true", help="also replay the assigned graph")
    args = parser.parse_args()
    if args.solver:
        run(args.solver.resolve(), args.full)
    else:
        with tempfile.TemporaryDirectory() as d:
            solver = Path(d) / "bound"
            subprocess.run([os.environ.get("CXX", "c++"), "-O2", "-std=c++20",
                            str(Path(__file__).with_name("bound.cpp")), "-o", solver], check=True)
            run(solver, args.full)
