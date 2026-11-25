"""Regression controls for the Boolean verifier. Run directly with Python 3."""
from verify_candidate import ExtremalTests, incidence_rows, star_circuit


def extend(circuit, op, operands):
    circuit["gates"].append([op, operands])
    circuit["output"] = 41 + len(circuit["gates"])
    return circuit["output"]


def check_counterexample(result, expected):
    assert not result["correct"]
    case = result["counterexample"]
    assert case["expected"] is expected and case["observed"] is not expected
    direct = any((line - point) % 21 in {0, 5, 7, 17, 20}
                 for point in case["points"] for line in case["lines"])
    assert direct is expected


def main():
    tests = ExtremalTests()
    assert (tests.edge_count, tests.false_count) == (105, 25237)
    assert len(tests.examples) == len(set(tests.examples)) == 25342

    # Independent direct incidence predicate and maximality check on each output.
    rows = [sum(1 << line for line in range(21)
                if (line - point) % 21 in {0, 5, 7, 17, 20}) for point in range(21)]
    assert rows == incidence_rows()
    full = (1 << 21) - 1
    for case in tests.examples[tests.edge_count:]:
        points, lines = case & full, case >> 21
        neighbors = 0
        for point, row in enumerate(rows):
            if points & (1 << point):
                neighbors |= row
            else:
                assert row & lines
        assert lines == full ^ neighbors

    star = star_circuit()
    result = tests.check(star)
    assert result == {"correct": True, "or_gates": 104, "and_gates": 21,
                      "matches_103_or_budget": False}

    # Keep all wire indices stable by replacing the OR by a one-operand AND.
    bypasses = 0
    for index, (op, operands) in enumerate(star["gates"]):
        if op == "or":
            for kept in operands:
                gates = list(star["gates"])
                gates[index] = ["and", [kept]]
                failed = tests.check({"gates": gates, "output": star["output"]})
                assert failed["matches_103_or_budget"] and failed["or_gates"] == 103
                check_counterexample(failed, True)
                bypasses += 1
    assert bypasses == 208

    # Add the nonedge (point 0, line 1). All 105 genuine edge inputs still pass.
    extra = star_circuit()
    original = extra["output"]
    spurious = extend(extra, "and", [0, 22])
    extend(extra, "or", [original, spurious])
    check_counterexample(tests.check(extra), False)

    # Empty, unary, repeated and absent operands; absent/future reads are false.
    padded = star_circuit()
    original = padded["output"]
    truth = extend(padded, "and", [])
    alias = extend(padded, "and", [original, truth])
    zero = extend(padded, "or", [])
    alias = extend(padded, "or", [alias, zero])
    alias = extend(padded, "and", [alias])
    alias = extend(padded, "or", [alias])
    alias = extend(padded, "and", [alias, alias])
    alias = extend(padded, "or", [alias, alias])
    future = 43 + len(padded["gates"])
    extend(padded, "or", [alias, future])
    assert tests.check(padded)["correct"]
    check_counterexample(tests.check({"gates": [], "output": 999}), True)
    check_counterexample(tests.check({"gates": [["and", []]], "output": 42}), False)
    check_counterexample(tests.check({"gates": [["or", []]], "output": 42}), True)

    invalid = [
        {"gates": [["not", [0]]], "output": 42},
        {"gates": [["or", [0, 1, 2]]], "output": 42},
        {"gates": [["or", [-1]]], "output": 42},
        {"gates": [["and", [True]]], "output": 42},
        {"gates": [], "output": -1},
        {"gates": [], "output": True},
    ]
    for circuit in invalid:
        try:
            tests.check(circuit)
        except ValueError:
            continue
        raise AssertionError("Expected invalid circuit rejection")
    print("25,342 distinct extremal tests; 104-OR star accepted; "
          "208 OR-operand bypasses rejected; nonedge false positive detected; "
          "4 wire-semantics controls and 6 invalid inputs passed.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run Python without -O so all regression checks are enabled.")
    main()
