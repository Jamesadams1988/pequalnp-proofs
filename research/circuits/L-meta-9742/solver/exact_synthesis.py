"""Generate one first-gate case of L-meta-9742 in DIMACS using Python 3."""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def nearby(name, *alternatives):
    for path in (HERE / name, HERE.parent / name, *(HERE / p for p in alternatives)):
        if path.is_file():
            return path
    return HERE / name


def load_problem(assignment_path, orbit_path):
    import importlib.util
    script = nearby("first_gate_symmetry.py", "../symmetry/first_gate_symmetry.py")
    spec = importlib.util.spec_from_file_location("first_gate_symmetry", script)
    symmetry = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(symmetry)
    assignment = json.loads(assignment_path.read_text())
    report = json.loads(orbit_path.read_text())
    regenerated = symmetry.orbit_report(assignment)
    if json.loads(json.dumps(regenerated)) != report:
        raise ValueError("orbit table differs from the group computation")
    edges = symmetry.parse_edges(assignment)
    cases = [(op, *orbit["representative"]) for orbit in report["pair_orbits"]
             for op in ("AND", "OR")]
    return edges, cases, symmetry


def required_case_ids(edges, cases):
    """In a minimum circuit a first AND must recognize a minimal true edge."""
    return [case_id for case_id, (op, a, b) in enumerate(cases)
            if op == "OR" or (a, b) in edges]


def boundary_tests(left, right, edges):
    """Each left subset forces the entire compatible right subset of a maximal independent set."""
    neighborhoods = [0] * left
    for a, b in edges:
        if not (0 <= a < left <= b < left + right):
            raise ValueError("edges must run from the left to the right part")
        neighborhoods[a] |= 1 << (b - left)
    tests = [((1 << a) | (1 << b), True) for a, b in sorted(edges)]
    for subset in range(1 << left):
        compatible = (1 << right) - 1
        for a, neighbors in enumerate(neighborhoods):
            if subset & (1 << a):
                compatible &= ~neighbors
        closure = sum(1 << a for a, neighbors in enumerate(neighborhoods)
                      if not neighbors & compatible)
        if closure == subset:
            tests.append((subset | (compatible << left), False))
    return tests


def exactly_one(selectors, prefixes):
    yield selectors
    yield (-selectors[0], prefixes[0])
    for i in range(1, len(selectors) - 1):
        yield (-selectors[i], prefixes[i])
        yield (-prefixes[i - 1], prefixes[i])
        yield (-selectors[i], -prefixes[i - 1])
    yield (-selectors[-1], -prefixes[-1])


class Gate:
    def __init__(self, source_count, test_count, reserve):
        self.op = reserve(1)[0]  # true selects OR
        self.choices = [reserve(source_count) for _ in range(2)]
        self.prefix = [reserve(source_count - 1) for _ in range(2)]
        self.ports = [reserve(test_count) for _ in range(2)]
        self.outputs = reserve(test_count)


class Encoding:
    def __init__(self, inputs, count, tests, first):
        if inputs < 2 or count < 1 or first[0] not in ("AND", "OR"):
            raise ValueError("invalid synthesis parameters")
        if not (0 <= first[1] < first[2] < inputs):
            raise ValueError("first-gate inputs must be an ordered distinct pair")
        self.inputs = inputs
        self.tests = tests
        self.first = first
        self.variables = 0
        self.gates = [Gate(inputs + i, len(tests), self.reserve) for i in range(count)]

    def reserve(self, length):
        start = self.variables + 1
        self.variables += length
        return range(start, start + length)

    def clause_count(self):
        # Two one-hot ports each contribute 3m-3 clauses for m sources.
        # Each primary source needs one mux clause, each gate source needs two.
        return 3 + len(self.tests) + sum(
            6 * (self.inputs + i) - 6
            + len(self.tests) * (2 * self.inputs + 4 * i + 6)
            for i in range(len(self.gates)))

    def clauses(self):
        op, a, b = self.first
        first = self.gates[0]
        yield (first.op if op == "OR" else -first.op,)
        yield (first.choices[0][a],)
        yield (first.choices[1][b],)
        for i, gate in enumerate(self.gates):
            for selectors, prefixes in zip(gate.choices, gate.prefix):
                yield from exactly_one(selectors, prefixes)
            for j, (mask, _) in enumerate(self.tests):
                x, y = (port[j] for port in gate.ports)
                z = gate.outputs[j]
                for selectors, port_value in zip(gate.choices, (x, y)):
                    for source in range(self.inputs):
                        yield (-selectors[source], port_value if mask >> source & 1 else -port_value)
                    for k in range(i):
                        choice = selectors[self.inputs + k]
                        source_value = self.gates[k].outputs[j]
                        yield (-choice, -source_value, port_value)
                        yield (-choice, source_value, -port_value)
                yield (gate.op, -x, -y, z)
                yield (gate.op, x, -z)
                yield (gate.op, y, -z)
                yield (-gate.op, x, y, -z)
                yield (-gate.op, -x, z)
                yield (-gate.op, -y, z)
        for z, (_, truth) in zip(self.gates[-1].outputs, self.tests):
            yield (z if truth else -z,)

    def dimacs(self, path):
        # Exclusive creation protects any pre-existing instance or user file.
        with path.open("x", encoding="ascii") as file:
            print("p cnf", self.variables, self.clause_count(), file=file)
            count = 0
            for clause in self.clauses():
                file.write(" ".join(map(str, clause)) + " 0\n")
                count += 1
            if count != self.clause_count():
                raise RuntimeError("DIMACS clause-count mismatch")


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assignment", type=Path, default=nearby("assignment.json", "../assigned.json"))
    parser.add_argument("--orbits", type=Path, default=nearby("first_gate_orbits.json", "../symmetry/first_gate_orbits.json"))
    parser.add_argument("--gates", type=int, default=62)
    parser.add_argument("--case", type=int, choices=range(28))
    parser.add_argument("--required-only", action="store_true",
                        help="show or select from just the 17 cases sufficient for the decision")
    parser.add_argument("--dimacs", type=Path, help="write one case to a new file")
    return parser


if __name__ == "__main__":
    parser = arguments()
    args = parser.parse_args()
    edges, cases, _ = load_problem(args.assignment, args.orbits)
    required = required_case_ids(edges, cases)
    if args.dimacs and args.case is None:
        parser.error("--dimacs requires an explicit --case")
    if args.required_only and args.case is not None and args.case not in required:
        parser.error("the selected case is a nonedge AND and is outside --required-only")
    tests = boundary_tests(13, 13, edges)
    selected = args.case if args.case is not None else required[0]
    encoding = Encoding(26, args.gates, tests, cases[selected])
    stats = {"gates": args.gates, "minimal_true": len(edges), "maximal_false": len(tests) - len(edges),
             "variables_per_case": encoding.variables, "clauses_per_case": encoding.clause_count(),
             "labeled_case_count": len(cases), "required_case_count": len(required),
             "required_case_ids": required,
             "cases": {i: cases[i] for i in (required if args.required_only else range(len(cases)))}}
    if args.dimacs:
        encoding.dimacs(args.dimacs)
        stats.update(selected_case=selected, dimacs=str(args.dimacs))
    print(json.dumps(stats, indent=2))
