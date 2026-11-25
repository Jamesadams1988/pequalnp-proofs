import unittest
from itertools import combinations

from monotone_search import boundary, search


def forward_minima(n, limit):
    # Independent breadth-first enumeration on all rows. All previously
    # produced wires stay available, including both operands of every gate.
    inputs = frozenset(sum(((r >> i) & 1) << r for r in range(1 << n))
                       for i in range(n))
    sizes = dict.fromkeys(inputs, 0)
    layer = {inputs}
    for depth in range(1, limit + 1):
        following = set()
        for wires in layer:
            for a, b in combinations(wires, 2):
                for out in (a & b, a | b):
                    if out not in wires:
                        sizes.setdefault(out, depth)
                        following.add(wires | {out})
        layer = following
    return sizes


class SearchTests(unittest.TestCase):
    def test_all_small_tables(self):
        for n, limit, expected_count in ((2, 2, 2), (3, 4, 9), (4, 4, 114)):
            applicable = 0
            sizes = forward_minima(n, limit)
            for table in range(1 << (1 << n)):
                try:
                    boundary(table, n)
                except ValueError:
                    continue
                applicable += 1
                for budget in range(n - 2, limit + 1):
                    witness, _ = search(table, n, budget)
                    self.assertEqual(witness is not None, sizes.get(table, limit + 1) <= budget,
                                     (n, hex(table), budget))
            self.assertEqual(applicable, expected_count)

    def test_assigned_table(self):
        self.assertIsNone(search(0xe8a8a8a8e8008800, 6, 8)[0])
        self.assertEqual(len(search(0xe8a8a8a8e8008800, 6, 9)[0]), 9)

    def test_rejects_inapplicable_tables(self):
        for table, n in ((0, 3), (0b0110, 2), (-1, 2), (1 << 16, 4)):
            with self.assertRaises(ValueError):
                search(table, n, 4)


if __name__ == "__main__":
    unittest.main()
