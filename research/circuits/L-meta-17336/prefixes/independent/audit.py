"""Independently verify the extremal leaf counts for the seven permitted first gates."""
import argparse
import itertools
import operator
from pathlib import Path
import subprocess
import sys


EDGES = ((0, 4), (0, 5), (1, 5), (0, 6), (2, 6), (3, 6),
         (1, 7), (2, 7), (4, 7), (1, 8), (3, 8), (5, 8))
FIRST_GATES = ((0, 5, 5), (1, 5, 6), (1, 5, 7), (1, 5, 8),
               (2, 5, 6), (2, 5, 7), (2, 5, 8))
SECOND_GATES = ({(0, i, i) for i in range(10)} |
                {(op, a, b) for op in (1, 2) for a, b in itertools.combinations(range(10), 2)})
OPS = (lambda x, y: ((1 << 512) - 1) ^ x, operator.and_, operator.or_)
DEFAULT_TABLE = Path(__file__).resolve().parent.parent / "expected.txt"


def target(mask):
    return any((mask >> a) & (mask >> b) & 1 for a, b in EDGES)


def samples():
    positives = [s for s in range(512) if target(s) and
                 all(not target(s ^ (1 << i)) for i in range(9) if (s >> i) & 1)]
    negatives = [s for s in range(512) if not target(s) and
                 all(target(s ^ (1 << i)) for i in range(9) if not (s >> i) & 1)]
    if (len(positives), len(negatives)) != (12, 13):
        raise ValueError("unexpected extremal sample sizes")
    return positives, negatives


def profiles(wires, positives, negatives):
    rectangles = set()
    for wire in wires:
        accept = sum(1 << i for i, s in enumerate(positives) if (wire >> s) & 1)
        reject = sum(1 << i for i, s in enumerate(negatives) if not (wire >> s) & 1)
        if accept and reject:
            rectangles.add((accept, reject))
    # A contained rectangle never changes which single leaves are available.
    return tuple(sorted((a, b) for a, b in rectangles if not any(
        (a, b) != (c, d) and a & c == a and b & d == b for c, d in rectangles)))


def read_table(path):
    lines = path.read_text().splitlines()
    if len(lines) != 707:
        raise ValueError(f"expected 707 lines, received {len(lines)}")
    for index, prefix in enumerate(FIRST_GATES):
        start = 101 * index
        heading = lines[start].split()
        if heading[:-1] != ["first", *map(str, prefix), "baseline", "leaves"]:
            raise ValueError(f"invalid heading on line {start + 1}")
        rows = {}
        for line in lines[start + 1:start + 101]:
            gate, a, b, cost = map(int, line.split())
            rows[gate, a, b] = cost
        if rows.keys() != SECOND_GATES:
            raise ValueError(f"missing or duplicated secondary gate for {prefix}")
        yield prefix, int(heading[-1]), rows


def solve(runner, key):
    runner.stdin.write(f"{len(key)} " + " ".join(f"{a} {b}" for a, b in key) + "\n")
    runner.stdin.flush()
    response = runner.stdout.readline()
    if not response:
        raise RuntimeError("solver stopped before returning a leaf count")
    return int(response)


def audit(path, executable, full):
    positives, negatives = samples()
    inputs = [sum(1 << s for s in range(512) if (s >> i) & 1) for i in range(9)]
    blocks = list(read_table(path))
    cache = {}
    verified = 0
    with subprocess.Popen([str(executable.resolve())], stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, text=True) as runner:
        try:
            for prefix, baseline, rows in blocks:
                first, left, right = prefix
                wires = inputs + [OPS[first](inputs[left], inputs[right])]
                cases = [("baseline", profiles(wires, positives, negatives), baseline)]
                for (gate, a, b), cost in rows.items():
                    second = OPS[gate](wires[a], wires[b])
                    key = profiles([*wires, second], positives, negatives)
                    cases.append(((gate, a, b), key, cost))
                selected = cases if full else [cases[0]] + [
                    next(case for case in cases[1:] if case[2] == n)
                    for n in sorted(set(rows.values()))]
                for _, key, _ in selected:
                    if key not in cache:
                        cache[key] = solve(runner, key)
                checked = 0
                for label, key, expected in cases:
                    if key not in cache:
                        continue
                    if cache[key] != expected:
                        raise ValueError(f"first {prefix}, {label}: table gives {expected}, "
                                         f"computed {cache[key]}")
                    checked += 1
                verified += checked
                print(f"First {prefix}: verified {checked} of 101 entries.", flush=True)
        finally:
            runner.stdin.close()
        if runner.wait() != 0:
            raise RuntimeError("solver exited unsuccessfully")
    print(f"Verified {verified} of 707 entries using {len(cache)} distinct calculations.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected", type=Path, default=DEFAULT_TABLE,
                        help="table to check (default: ../expected.txt in the parent directory)")
    parser.add_argument("--solver", type=Path, required=True, help="compiled split.cpp executable")
    parser.add_argument("--all", action="store_true", help="recompute every table entry")
    args = parser.parse_args()
    try:
        audit(args.expected, args.solver, args.all)
    except (ValueError, OSError, RuntimeError) as error:
        print(f"Audit failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
