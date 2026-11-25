"""Generate exact synthesis instances, check the witness, and replay four LRAT proofs."""
import argparse
from itertools import combinations
from pathlib import Path
import shutil
import subprocess

TABLE = 4008372968 * 2**32 + 3941133032
COFACTOR = 4008372968
WITNESS = [
    (4, 5, "and"), (3, 6, "and"), (2, 7, "or"), (1, 8, "and"),
    (0, 9, "or"), (1, 2, "or"), (3, 6, "or"), (11, 12, "or"),
    (10, 13, "and"),
]


def check(condition, message):
    if not condition:
        raise ValueError(message)


def evaluate(n, gates):
    """Return one bit per input row. Every gate is checked for legal operands."""
    mask = (1 << (1 << n)) - 1
    wires = [sum(((row >> i) & 1) << row for row in range(1 << n)) for i in range(n)]
    for a, b, op in gates:
        check(0 <= a < len(wires) and 0 <= b < len(wires), "bad operand")
        if op == "and":
            value = wires[a] & wires[b]
        elif op == "or":
            value = wires[a] | wires[b]
        else:
            check(op == "not" and a == b, "bad operation")
            value = mask ^ wires[a]
        wires.append(value)
    return wires[-1]


def verify_target():
    check(evaluate(6, WITNESS) == TABLE, "six-input witness differs")
    check(TABLE >> 32 == COFACTOR, "wrong cofactor")
    for n, table in [(6, TABLE), (5, COFACTOR)]:
        for i in range(n):
            check(any(((table >> x) ^ (table >> (x ^ (1 << i)))) & 1 for x in range(1 << n)),
                  "inessential variable")
    check(evaluate(6, WITNESS[:-1] + [(10, 13, "or")]) != TABLE, "damaged witness accepted")
    check(all((TABLE >> row) & 1 for row in [3, 61, 62]) and
          all(not ((TABLE >> row) & 1) for row in [0, 1, 2, 60]),
          "minterm/cut certificate differs")
    print("Nine-gate witness matches all 64 rows, damaged witness rejected, all inputs essential.", flush=True)


def instance(size, allow_not):
    """Synthesize a minimum 5-input circuit of exactly size gates on all 32 rows."""
    n = 5
    variables = 0
    clauses = []

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    values = [[fresh() for _ in range(32)] for _ in range(n + size)]
    for i in range(n):
        for row, value in enumerate(values[i]):
            clauses.append([value if (row >> i) & 1 else -value])
    for row, value in enumerate(values[-1]):
        clauses.append([value if (COFACTOR >> row) & 1 else -value])

    options = []
    for j in range(n, n + size):
        selectors = {}
        for a in range(j):
            for b in range(a + 1, j):
                for op in ("and", "or"):
                    s = selectors[a, b, op] = fresh()
                    for x, y, z in zip(values[a], values[b], values[j]):
                        if op == "and":
                            clauses.extend([[-s, -z, x], [-s, -z, y], [-s, z, -x, -y]])
                        else:
                            clauses.extend([[-s, z, -x], [-s, z, -y], [-s, -z, x, y]])
            if allow_not:
                s = selectors[a, a, "not"] = fresh()
                for x, z in zip(values[a], values[j]):
                    clauses.extend([[-s, z, x], [-s, -z, -x]])
        clauses.append(list(selectors.values()))
        clauses.extend([-a, -b] for a, b in combinations(selectors.values(), 2))
        options.append(selectors)

    for wire in range(n + size - 1):
        clauses.append([s for opts in options for (a, b, _), s in opts.items() if wire in (a, b)])
    for j in range(1, size):
        for earlier, s in options[j - 1].items():
            for later, t in options[j].items():
                if n + j - 1 not in later[:2] and earlier > later:
                    clauses.append([-s, -t])
    return variables, clauses, options


def solve(solver, directory, size, allow_not):
    variables, clauses, options = instance(size, allow_not)
    label = f"u{size}" if allow_not else f"m{size}"
    stem = directory / label
    cnf = stem.with_suffix(".cnf")
    with cnf.open("w") as out:
        print("p cnf", variables, len(clauses), file=out)
        for clause in clauses:
            print(*clause, 0, file=out)
    args = [solver, "--quiet", "--check=true", str(cnf)]
    if allow_not:
        args[1:1] = ["--lrat=true", "--binary=false"]
        args.append(str(stem.with_suffix(".lrat")))
    run = subprocess.run(args, capture_output=True, text=True)
    if allow_not:
        check(run.returncode == 20, f"{label} expected UNSAT, exit {run.returncode}: {run.stderr}")
        print(f"{label} UNSAT, {variables} variables and {len(clauses)} clauses", flush=True)
    else:
        check(run.returncode == 10, f"{label} expected SAT, exit {run.returncode}: {run.stderr}")
        model = {int(word) for line in run.stdout.splitlines() if line.startswith("v ")
                 for word in line.split()[1:] if word != "0"}
        check(len(model) == variables and all(-literal not in model for literal in model),
              "model assigns conflicting literals or omits variables")
        check(all(any(lit in model for lit in clause) for clause in clauses), "unsatisfied model clause")
        gates = []
        for opts in options:
            chosen = [gate for gate, selector in opts.items() if selector in model]
            check(len(chosen) == 1, "non-unique gate")
            gates.extend(chosen)
        check(evaluate(5, gates) == COFACTOR, "decoded SAT model differs")
        print(f"{label} SAT; decoded eight-gate monotone circuit matches all 32 rows.", flush=True)
    return stem


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--cadical", default="cadical")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    solver = shutil.which(args.cadical)
    check(lean is not None and solver is not None, "pass paths to Lean and CaDiCaL or add them to PATH")
    args.output.mkdir(parents=True, exist_ok=True)
    verify_target()
    stems = [solve(solver, args.output, size, True) for size in range(4, 8)]
    solve(solver, args.output, 8, False)
    checker = Path(__file__).resolve().with_name("ReplayFinite.lean")
    subprocess.run([lean, "--run", str(checker), *(str(s) for s in stems)], check=True)
    print("Five-input cofactor minimum 8. Six-input unrestricted and monotone minima both 9.")


if __name__ == "__main__":
    main()
