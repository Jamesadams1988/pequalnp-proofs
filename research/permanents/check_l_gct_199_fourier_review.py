"""Exact coefficient replay for the L-gct-199 Fourier-coordinate search.

Run with Python 3.8 or later. Uses only the standard library.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, prod


MODES = tuple(product(range(1, 4), range(1, 5)))
DEGREES = (2, 3, 4)


@lru_cache(maxsize=None)
def injection_sum(order, frequencies):
    """Sum over distinct positions and reduce at an exact primitive root."""
    histogram = [0] * order
    for positions in permutations(range(order), len(frequencies)):
        exponent = sum(a * r for a, r in zip(frequencies, positions)) % order
        histogram[exponent] += 1

    if order == 4:
        # The minimal polynomial of i is x^2 + 1.
        remainder = (histogram[0] - histogram[2], histogram[1] - histogram[3])
    else:
        # The minimal polynomial of the primitive fifth root is 1+x+x^2+x^3+x^4.
        remainder = tuple(count - histogram[4] for count in histogram[:4])

    assert not any(remainder[1:]), (order, frequencies, remainder)
    return remainder[0]


def nonzero_coefficients(degree):
    coefficients = {}
    for multiset in combinations_with_replacement(MODES, degree):
        rows, columns = zip(*multiset)
        labeled_sum = injection_sum(4, rows) * injection_sum(5, columns)
        multiplicity_factor = prod(factorial(count) for count in Counter(multiset).values())
        coefficient, remainder = divmod(labeled_sum, multiplicity_factor)
        assert remainder == 0
        assert bool(coefficient) == (sum(rows) % 4 == 0 and sum(columns) % 5 == 0)
        if coefficient:
            coefficients[multiset] = coefficient
    return coefficients


def first_obstruction(support, coefficients):
    available = set(support)
    return next((monomial for monomial in coefficients if available.issuperset(monomial)), None)


def direct_matching_sums_mod_41(amplitudes):
    """Check a named example by the literal matching sums in the pinned statement."""
    prime, row_root, column_root = 41, 9, 10
    assert pow(row_root, 2, prime) == prime - 1
    assert column_root != 1 and pow(column_root, 5, prime) == 1
    matrix = [
        [
            sum(value * pow(row_root, a * r, prime) * pow(column_root, b * c, prime)
                for (a, b), value in amplitudes.items()) % prime
            for c in range(5)
        ]
        for r in range(4)
    ]
    assert all(sum(row) % prime == 0 for row in matrix)
    assert all(sum(column) % prime == 0 for column in zip(*matrix))
    return tuple(
        sum(
            prod(matrix[r][c] for r, c in zip(rows, columns))
            for rows in combinations(range(4), degree)
            for columns in permutations(range(5), degree)
        ) % prime
        for degree in DEGREES
    )


def main():
    supports = list(combinations(MODES, 5))
    survivors = supports
    coefficients_by_degree = {degree: nonzero_coefficients(degree) for degree in DEGREES}
    expected_counts = {2: (6, 192, 192), 3: (16, 84, 4), 4: (73, 0, 0)}
    print(f"coordinate 5-spaces: {len(supports)}")
    assert len(supports) == 792
    for degree, coefficients in coefficients_by_degree.items():
        alone = [support for support in supports if first_obstruction(support, coefficients) is None]
        if degree == 4:
            for support in survivors:
                obstruction = first_obstruction(support, coefficients)
                print(f"quartic falsifier: {support} -> {obstruction}: {coefficients[obstruction]}")
        survivors = [support for support in survivors if first_obstruction(support, coefficients) is None]
        counts = (len(coefficients), len(alone), len(survivors))
        assert counts == expected_counts[degree]
        print(f"degree {degree}: nonzero monomials {counts[0]}, alone {counts[1]}, cumulative {counts[2]}")

    # This three-mode space has no obstruction in any of the three degrees.
    control = ((1, 1), (2, 1), (3, 1))
    assert all(first_obstruction(control, coefficients) is None
               for coefficients in coefficients_by_degree.values())
    print(f"positive control: {control} has all matching sums identically zero")

    # In the first quadratic/cubic survivor, turn on only the two quartic-obstructing modes.
    values = direct_matching_sums_mod_41({(1, 1): 1, (1, 2): 1})
    assert values == (0, 0, 120 % 41)
    print(f"direct mod 41 falsifier F_(1,1)+F_(1,2): {values}")
    values = direct_matching_sums_mod_41({(1, 1): 1, (2, 1): 2, (3, 1): 3})
    assert values == (0, 0, 0)
    print(f"direct mod 41 positive control: {values}")


if __name__ == "__main__":
    main()
