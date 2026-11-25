"""Compute the L-gct-194 coefficient table by processing one row at a time."""

from collections import defaultdict


ZERO = (0, 0)
ONE = (1, 0)
CIRCULANT = (ONE, (0, 1), (0, -1), (-1, 0))


def rectangular_permanent(appended_first_coefficient):
    rows = [
        [CIRCULANT[(column - row) % 4] for column in range(4)]
        for row in range(4)
    ]
    rows.append([(appended_first_coefficient, 0), (-1, 0), ZERO, ZERO])

    # A mask marks the columns already matched to rows in the current prefix.
    # Each polynomial maps (degree of c, degree of d) to (real, imaginary).
    states = [defaultdict(lambda: ZERO) for _ in range(16)]
    states[0][(0, 0)] = ONE
    for row, entries in enumerate(rows):
        next_states = [coefficients.copy() for coefficients in states]
        for mask, coefficients in enumerate(states):
            for column, (entry_real, entry_imag) in enumerate(entries):
                column_bit = 1 << column
                if mask & column_bit:
                    continue
                target = next_states[mask | column_bit]
                for (degree_c, degree_d), (real, imag) in coefficients.items():
                    degree = (degree_c, degree_d)
                    old_real, old_imag = target[degree]
                    target[degree] = (old_real + real, old_imag + imag)

                    if row == 4:
                        degree = (degree_c, degree_d + 1)
                    else:
                        degree = (degree_c + 1, degree_d)
                    old_real, old_imag = target[degree]
                    target[degree] = (
                        old_real + real * entry_real - imag * entry_imag,
                        old_imag + real * entry_imag + imag * entry_real,
                    )
        states = next_states

    return {degree: value for degree, value in states[15].items() if value != ZERO}


def main():
    published = rectangular_permanent(appended_first_coefficient=1)
    mutated = rectangular_permanent(appended_first_coefficient=2)
    if published != {(0, 0): (120, 0)}:
        raise SystemExit(f"Published coefficient check failed: {published}")
    if mutated != {(0, 0): (120, 0), (0, 1): (24, 0)}:
        raise SystemExit(f"Mutation coefficient check failed: {mutated}")

    print("degree(c,d)  published (Re, Im)  w_0=2 (Re, Im)")
    for degree_d in range(2):
        for degree_c in range(5 - degree_d):
            degree = (degree_c, degree_d)
            published_coefficient = str(published.get(degree, ZERO))
            mutated_coefficient = mutated.get(degree, ZERO)
            print(f"{str(degree):12} {published_coefficient:19} {mutated_coefficient}")
    print("PASS: 9 coefficient pairs checked per case; mutation residual = 24*d")


if __name__ == "__main__":
    main()
