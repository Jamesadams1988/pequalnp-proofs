"""Replay the small SAT tests and verify every clause on the relabeled 63-gate witness."""
import argparse
import ctypes
import ctypes.util
import json
import re
from pathlib import Path
from exact_synthesis import Encoding, boundary_tests, load_problem, nearby, required_case_ids


def z3_status(encoding):
    """Use the optional system libz3 shared library for tiny SAT regression cases."""
    lib = ctypes.util.find_library("z3")
    if not lib:
        raise RuntimeError("small SAT regressions require libz3")
    z3 = ctypes.CDLL(lib)
    ptr = ctypes.c_void_p
    signatures = {
        "Z3_mk_config": (ptr, []), "Z3_mk_context": (ptr, [ptr]),
        "Z3_del_config": (None, [ptr]), "Z3_del_context": (None, [ptr]),
        "Z3_eval_smtlib2_string": (ctypes.c_char_p, [ptr, ctypes.c_char_p]),
    }
    for name, (result, parameters) in signatures.items():
        fn = getattr(z3, name)
        fn.restype, fn.argtypes = result, parameters
    declarations = [f"(declare-const x{i} Bool)" for i in range(1, encoding.variables + 1)]
    clauses = list(encoding.clauses())
    if len(clauses) != encoding.clause_count():
        raise ValueError("small-instance clause count differs")
    for clause in clauses:
        literals = " ".join(f"x{v}" if v > 0 else f"(not x{-v})" for v in clause)
        declarations.append(f"(assert (or {literals}))")
    declarations.append("(check-sat)")
    cfg = z3.Z3_mk_config()
    ctx = z3.Z3_mk_context(cfg)
    try:
        return z3.Z3_eval_smtlib2_string(ctx, "\n".join(declarations).encode()).decode().strip()
    finally:
        z3.Z3_del_context(ctx)
        z3.Z3_del_config(cfg)


def small_checks():
    single = boundary_tests(1, 1, {(0, 1)})
    star = boundary_tests(2, 1, {(0, 2), (1, 2)})
    cases = [(2, 1, single, ("AND", 0, 1), "sat"),
             (2, 1, single, ("OR", 0, 1), "unsat"),
             (3, 1, star, ("OR", 0, 1), "unsat"),
             (3, 2, star, ("OR", 0, 1), "sat"),
             (3, 2, star, ("AND", 0, 1), "unsat"),
             (3, 3, star, ("OR", 0, 1), "sat"),
             (3, 4, star, ("AND", 0, 1), "sat")]
    results = []
    for inputs, gates, tests, first, expected in cases:
        actual = z3_status(Encoding(inputs, gates, tests, first))
        if actual != expected:
            raise ValueError(f"expected {expected}, got {actual}")
        results.append({"inputs": inputs, "gates": gates, "first": first, "solver_status": actual})
    return results


def witness_model(encoding, circuit):
    if len(circuit) != len(encoding.gates):
        raise ValueError("witness size differs")
    values = bytearray(encoding.variables + 1)
    for i, ((op, a, b), gate) in enumerate(zip(circuit, encoding.gates)):
        values[gate.op] = op == "OR"
        for wire, choices, prefix in zip((a, b), gate.choices, gate.prefix):
            if not 0 <= wire < encoding.inputs + i:
                raise ValueError("non-topological witness")
            values[choices[wire]] = True
            for k in range(wire, len(prefix)):
                values[prefix[k]] = True
        for j, (mask, _) in enumerate(encoding.tests):
            def source(wire):
                if wire < encoding.inputs:
                    return mask >> wire & 1
                return values[encoding.gates[wire - encoding.inputs].outputs[j]]
            x, y = source(a), source(b)
            values[gate.ports[0][j]], values[gate.ports[1][j]] = x, y
            values[gate.outputs[j]] = (x | y) if op == "OR" else (x & y)
    return values


def target_check(assignment, orbit_path, witness):
    edges, cases, symmetry = load_problem(assignment, orbit_path)
    required = required_case_ids(edges, cases)
    if required != sorted([*range(1, 28, 2), 8, 14, 24]):
        raise ValueError("unexpected required first-gate case IDs")
    tests = boundary_tests(13, 13, edges)
    transpose = {(b - 13, a + 13) for a, b in edges}
    swapped = [(((mask >> 13) | ((mask & 8191) << 13)), value)
               for mask, value in boundary_tests(13, 13, transpose)]
    if set(tests) != set(swapped) or len(set(tests)) != 737:
        raise ValueError("boundary disagreement")
    source = witness.read_text()
    body = source.split("def circuit : Circuit :=", 1)[1].split("theorem parameters", 1)[0]
    circuit = [(op.upper(), int(a), int(b))
               for op, a, b in re.findall(r"⟨\.(and|or),\s*\[(\d+),\s*(\d+)\]⟩", body)]
    if len(circuit) != 63 or not re.search(r"\],\s*88⟩", body):
        raise ValueError("unexpected witness circuit or output wire")
    group, _, _ = symmetry.enumerate_group(edges)
    op, a, b = circuit[0]
    rep_a, rep_b = min(tuple(sorted((g[a], g[b]))) for g in group)
    relabel = min(g for g in group if tuple(sorted((g[a], g[b]))) == (rep_a, rep_b))
    circuit = [(op, *(sorted(relabel[u] if u < 26 else u for u in (a, b))))
               for op, a, b in circuit]
    case = cases.index(circuit[0])
    encoding = Encoding(26, len(circuit), tests, cases[case])
    values = witness_model(encoding, circuit)
    checked = 0
    for clause in encoding.clauses():
        if not any(values[abs(lit)] == (lit > 0) for lit in clause):
            raise ValueError(f"witness falsifies clause {checked + 1}")
        checked += 1
    if checked != encoding.clause_count():
        raise ValueError("target clause count differs")
    if case not in required:
        raise ValueError("expected the known witness to occupy a retained case")
    return {"gates": len(circuit), "case": case, "first": circuit[0],
            "required_case_count": len(required),
            "boundary_tests": len(tests), "variables": encoding.variables, "satisfied_clauses": checked}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assignment", type=Path, default=nearby("assignment.json", "../assigned.json"))
    parser.add_argument("--orbits", type=Path, default=nearby("first_gate_orbits.json", "../symmetry/first_gate_orbits.json"))
    parser.add_argument("--witness", type=Path, default=nearby("Upper63.lean", "../upper/Upper63.lean", "../upper/lean/Upper63.lean"))
    parser.add_argument("--target-only", action="store_true", help="skip tests that require system libz3")
    args = parser.parse_args()
    result = {} if args.target_only else {"small_z3_tests": small_checks()}
    result["target_witness"] = target_check(args.assignment, args.orbits, args.witness)
    print(json.dumps(result, indent=2))
