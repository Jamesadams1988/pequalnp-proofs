"""Certify the minimum unrestricted and monotone gate counts for L-meta-13049/13050.

Run with Python 3.10 or later. This file uses only the standard library.

Why enumeration of read-once AND/OR formulas suffices:
Trace the output backwards through actual operands. A forward, self or missing
wire read gives false at evaluation time, so it adds no predecessor.
NOT depends only on its first input. Repeated operands give just one predecessor.
An unavailable output gives constant false and an input output depends on at
most one variable. Otherwise the traced graph with g gate vertices and k input
vertices is connected. It has at least g+k-1 distinct edges and at most 2g,
since each gate has at most two incoming edges. All six inputs are essential,
so k=6 and g>=5. At size <=5 both inequalities must be equalities. Every gate
is reachable and has two distinct, available, effective predecessor wires.
This excludes NOT and nullary/unary gates. The underlying connected graph
has vertices minus one edges, hence is a tree, with the output as its root.
Thus its subtrees have disjoint variables and every input is used exactly once.
The dynamic program below enumerates all such trees by their two root subtrees.
"""
from functools import cache
from itertools import combinations


def require(condition, message):
    if not condition:
        raise ValueError(message)


def variable_tables(variable_count):
    rows = range(1 << variable_count)
    return tuple(sum((row >> i & 1) << row for row in rows)
                 for i in range(variable_count))


def evaluate(inputs, gates, output):
    """Evaluate all rows in parallel, matching Lean getD and NOT/headD semantics."""
    full = (1 << (1 << len(inputs))) - 1
    wires = list(inputs)

    def read(index):
        return wires[index] if 0 <= index < len(wires) else 0

    for op, arguments in gates:
        require(len(arguments) <= 2, "fan-in exceeded")
        if op == 'not':
            value = full ^ (read(arguments[0]) if arguments else 0)
        elif op == 'and':
            value = full
            for argument in arguments:
                value &= read(argument)
        elif op == 'or':
            value = 0
            for argument in arguments:
                value |= read(argument)
        else:
            raise ValueError(f"unsupported gate {op}")
        wires.append(value)
    return read(output)


def essential_witnesses(table, variable_count):
    witnesses = []
    for i in range(variable_count):
        for low in range(1 << variable_count):
            if low >> i & 1:
                continue
            high = low | (1 << i)
            if (table >> low ^ table >> high) & 1:
                witnesses.append((low, high))
                break
        else:
            raise ValueError(f"variable {i} is inessential")
    return witnesses


def read_once_families(inputs):
    @cache
    def family(mask):
        if mask.bit_count() == 1:
            return {inputs[mask.bit_length() - 1]}
        result = set()
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if left < right:
                for a in family(left):
                    for b in family(right):
                        result.add(a & b)
                        result.add(a | b)
            left = (left - 1) & mask
        return result

    return family


def main():
    n = 6
    inputs = variable_tables(n)
    target = (4277074666 << 32) + 4277074602
    full = (1 << (1 << n)) - 1
    # Gate and missing-wire controls are independent of the target circuit.
    require(evaluate(inputs, [('not', [0, 1])], 6) == full ^ inputs[0], "NOT second input")
    require(evaluate(inputs, [('not', [7, 0]), ('and', [0, 1])], 6) == full, "forward reference")
    require(evaluate(inputs, [('and', [])], 6) == full, "empty AND")
    require(evaluate(inputs, [('or', [])], 6) == 0, "empty OR")
    require(evaluate(inputs, [('not', [])], 6) == full, "empty NOT")
    require(evaluate(inputs, [('or', [2, 2])], 6) == inputs[2], "repeated input")
    require(evaluate(inputs, [], 12) == 0, "missing output")

    gates = [('and', [2, 5]), ('or', [4, 6]), ('and', [1, 7]),
             ('and', [2, 3]), ('or', [9, 8]), ('or', [0, 10])]
    require(len(gates) == 6 and evaluate(inputs, gates, 11) == target, "six-gate upper bound")
    witnesses = essential_witnesses(target, n)
    print("Essential flip witnesses in variable order", witnesses)

    families = read_once_families(inputs)
    for k in range(1, n + 1):
        counts = {len(families(sum(1 << i for i in support)))
                  for support in combinations(range(n), k)}
        require(len(counts) == 1, "permuted support counts differ")
        print(f"{k} variables per fixed support give {counts.pop()} distinct read-once tables")

    all_variables = families((1 << n) - 1)
    a, b, c, d, e, f = inputs
    # Positive control uses every variable once. The negative control restricts
    # to 3-variable majority when d=e=f=0, which has no read-once formula.
    positive_control = (a & b) | ((c | d) & (e | f))
    majority_control = (a & b) | (a & c) | (b & c) | d | e | f
    require(positive_control in all_variables, "read-once positive control")
    require(majority_control not in all_variables, "majority negative control")
    require(target not in all_variables, "five-gate solution found")
    print(f"Target {target:#018x} is absent; its six-gate monotone witness matches all 64 rows.")
    print("Both minimum sizes equal 6. All controls passed.")


if __name__ == '__main__':
    main()
