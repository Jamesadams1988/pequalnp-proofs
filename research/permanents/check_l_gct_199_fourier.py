"""Exhaust the five-mode coordinate planes in the 4-by-5 Fourier basis."""

from itertools import combinations, combinations_with_replacement, permutations, product


ROWS = range(4)
COLUMNS = range(5)
MODES = tuple(product(range(1, 4), range(1, 5)))
PHASE = {
    mode: tuple(
        tuple((5 * mode[0] * row + 4 * mode[1] * column) % 20 for column in COLUMNS)
        for row in ROWS
    )
    for mode in MODES
}


def cyclotomic_remainder(phase_counts):
    """Reduce a coefficient modulo Φ20 = z^8 - z^6 + z^4 - z^2 + 1."""
    coefficients = list(phase_counts)
    for degree in range(19, 7, -1):
        leading = coefficients[degree]
        coefficients[degree - 2] += leading
        coefficients[degree - 4] -= leading
        coefficients[degree - 6] += leading
        coefficients[degree - 8] -= leading
    return tuple(coefficients[:8])


def is_centered(mode):
    grid = PHASE[mode]
    return all(
        not any(cyclotomic_remainder(tuple(line.count(exponent) for exponent in range(20))))
        for line in (*grid, *zip(*grid))
    )


def nonzero_coefficients(degree):
    """Sum the monomial coefficients over distinct columns and increasing rows."""
    row_sets = tuple(combinations(ROWS, degree))
    column_assignments = tuple(permutations(COLUMNS, degree))
    nonzero = {}

    for monomial in combinations_with_replacement(MODES, degree):
        counts = [0] * 20
        for mode_order in set(permutations(monomial)):
            for rows in row_sets:
                phases = tuple(PHASE[mode][row] for row, mode in zip(rows, mode_order))
                for columns in column_assignments:
                    exponent = sum(phase[column] for phase, column in zip(phases, columns))
                    counts[exponent % 20] += 1
        remainder = cyclotomic_remainder(counts)
        if any(remainder):
            nonzero[monomial] = remainder

    return nonzero


def main():
    centered = sum(map(is_centered, MODES))
    print(f"centered Fourier modes: {centered}/{len(MODES)}")
    assert centered == len(MODES)
    planes = list(combinations(MODES, 5))
    print(f"five-mode planes: {len(planes)}")

    for degree in (2, 3, 4):
        blockers = nonzero_coefficients(degree)
        survivors = []
        excluded = []

        for plane in planes:
            for monomial in combinations_with_replacement(plane, degree):
                if monomial in blockers:
                    excluded.append((plane, monomial, blockers[monomial]))
                    break
            else:
                survivors.append(plane)

        print(f"degree {degree}: {len(survivors)}/{len(planes)} cumulative survivors")
        reported_exclusions = excluded if degree == 4 else excluded[:1]
        for plane, monomial, coefficient in reported_exclusions:
            print(f"  excluded plane: {plane}")
            print(f"  monomial modes: {monomial}")
            print(f"  coefficient in powers 0 through 7 of z: {coefficient}")
        planes = survivors

    for plane in planes:
        print(f"witness modes: {plane}")


if __name__ == "__main__":
    main()
