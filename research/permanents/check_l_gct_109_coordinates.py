"""Compare the Fourier formulas with the entry-coordinate formulas from upstream PR 26.

https://github.com/open-goat/pequalnp-proofs/pull/26
"""

from sympy import Matrix, Poly, expand, symbols

w, a, b, c, d = symbols('w a b c d')
u = Matrix([1, w, w**2])
v = Matrix([1, w**2, w])
t = a*u*u.T + b*u*v.T + c*v*u.T + d*v*v.T
A, B, C, D = t[0, 0], t[0, 1], t[1, 0], t[1, 1]
q = (2*A**2 + 2*A*B + 2*A*C + A*D + 2*B**2 + B*C
     + 2*B*D + 2*C**2 + 2*C*D + 2*D**2)
cubic = (2*A**2*D + 4*A*B*C + 4*A*B*D + 4*A*C*D
         + 2*A*D**2 + 2*B**2*C + 2*B*C**2 + 4*B*C*D)


def reduce_root(polynomial):
    return Poly(expand(polynomial), w).rem(Poly(w**2 + w + 1, w)).as_expr().expand()


assert reduce_root(q - 9*(a*d + b*c)) == 0
assert reduce_root(cubic - 6*(a**3 + b**3 + c**3 + d**3)) == 0
assert reduce_root(q + A**2 - 9*(a*d + b*c)) != 0
print('PASS: both forms agree, and the modified coefficient is detected')
