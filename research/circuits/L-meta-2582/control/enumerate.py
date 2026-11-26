"""Enumerate two-input binary AO programs in nondecreasing operand order."""
from functools import cache
from itertools import combinations_with_replacement


def encode(x_count, y_count):
    return 1 << (4 * x_count + y_count)


def exponents(mask):
    return [(i // 4, i % 4) for i in range(16) if (mask >> i) & 1]


@cache
def multiply(left, right):
    result = 0
    for a, b in exponents(left):
        for c, d in exponents(right):
            result |= encode(min(3, a + c), min(3, b + d))
    return result


@cache
def classify(mask):
    pairs = exponents(mask)
    # Every parse uses both variables iff the circuit computes x AND y.
    if any(min(pair) == 0 for pair in pairs):
        return False, False
    if any(max(pair) <= 2 for pair in pairs):
        return False, False
    scalar = max(min(x for x, y in pairs), min(y for x, y in pairs))
    return scalar <= 2, scalar <= 1


def census(depth=5):
    counts = [[0, 0, 0] for _ in range(depth + 1)]

    def visit(wires, gates):
        if gates == depth:
            return
        result = counts[gates + 1]
        for a, b in combinations_with_replacement(wires, 2):
            for output in (a | b, multiply(min(a, b), max(a, b))):
                # Equal-valued wires still have distinct positions in "wires".
                result[0] += 1
                scalar_two, scalar_one = classify(output)
                result[1] += scalar_two
                result[2] += scalar_one
                visit(wires + (output,), gates + 1)

    visit((encode(1, 0), encode(0, 1)), 0)
    return counts[1:]


if __name__ == "__main__":
    x, y = encode(1, 0), encode(0, 1)
    both, either = multiply(x, y), x | y
    four = multiply(both, multiply(both, either))
    five = multiply(both, multiply(x, x) | multiply(y, y))
    assert exponents(four) == [(2, 3), (3, 2)]
    assert exponents(five) == [(1, 3), (3, 1)]
    counts = census()
    assert [row[0] for row in counts] == [6, 72, 1440, 43200, 1814400]
    assert counts[:4] == [[6, 0, 0], [72, 0, 0], [1440, 0, 0], [43200, 13, 0]]
    assert counts[4] == [1814400, 1905, 107]
    print("gates | program count | scalar<=2 and joint>2 | scalar<=1 and joint>2")
    for depth, row in enumerate(counts, start=1):
        print(depth, *row)
