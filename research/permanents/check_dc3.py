"""Exact coefficient checks for the doubly centered 3 by 3 permanent.

Run with Python 3 and SymPy 1.14 from any working directory.
"""

from itertools import permutations

from sympy import Matrix, Poly, expand, ones, symbols, zeros


a, b, c, d, z, omega = symbols("a b c d z omega")
cyclotomic = Poly(omega**2 + omega + 1, omega)


def reduce_cyclotomic(expression):
    """Reduce modulo omega² + omega + 1 by exact polynomial division."""
    return Poly(expand(expression), omega).rem(cyclotomic).as_expr()


def permanent_3(matrix):
    """Expand the permanent through its six permutations."""
    return sum(
        matrix[0, p[0]] * matrix[1, p[1]] * matrix[2, p[2]]
        for p in permutations(range(3))
    )


def check():
    u = Matrix([1, omega, omega**2])
    v = Matrix([1, omega**2, omega])
    t = a * u * u.T + b * u * v.T + c * v * u.T + d * v * v.T
    assert (t * ones(3, 1)).applyfunc(reduce_cyclotomic) == zeros(3, 1)
    assert (ones(1, 3) * t).applyfunc(reduce_cyclotomic) == zeros(1, 3)
    print("PASS: generic Fourier matrix has zero row and column sums")

    actual = permanent_3(ones(3, 3) + z * t)
    expected = 6 + 9 * (a * d + b * c) * z**2 + 6 * (a**3 + b**3 + c**3 + d**3) * z**3
    assert reduce_cyclotomic(actual - expected) == 0
    print("PASS: generic permanent matches all claimed coefficients")

    witness = u * (u - v).T
    assert witness[0, 1] == omega - omega**2
    assert reduce_cyclotomic(witness[0, 1]) != 0
    assert reduce_cyclotomic(permanent_3(ones(3, 3) + z * witness) - 6) == 0
    print("PASS: nonzero witness spans a constant-permanent line")

    negative_control = u * (u + v).T
    assert reduce_cyclotomic(permanent_3(ones(3, 3) + z * negative_control) - 6) == 12 * z**3
    print("PASS: negative control passes the quadratic test and fails the cubic test")


if __name__ == "__main__":
    check()
