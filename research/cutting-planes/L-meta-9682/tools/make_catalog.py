"""Generate the closed set of read-once K4 lines used by Column.lean."""
from column import reachable


def main():
    entries = [(mask, line) for mask, lines in enumerate(reachable()) for line in sorted(lines)]
    text = ',\n  '.join(f'({mask}, ⟨' + ','.join(map(str, line)) + '⟩)' for mask, line in entries)
    print('import PEqualNP.Defs\n\nnamespace K4Column\n')
    print('structure Line where\n  a : ℕ\n  b : ℕ\n  c : ℕ\n  d : ℕ\n  rhs : ℕ\n  deriving DecidableEq\n')
    print('def catalog : List (ℕ × Line) := [\n  ' + text + ']\n\nend K4Column')


if __name__ == '__main__':
    main()
