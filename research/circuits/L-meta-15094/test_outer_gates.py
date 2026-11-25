import unittest
from itertools import product

from outer_gates import dual, extensions, relabel


class ExtensionTests(unittest.TestCase):
    def test_projection(self):
        self.assertEqual(extensions(0b10, 1, 0), {0b10})
        self.assertEqual(extensions(0b10, 1, 1), {0b1000, 0b1110})
        self.assertEqual(len(extensions(0b10, 1, 2)), 8)

    def test_named_core_and_assigned_row(self):
        core = 0xe8a8a800
        self.assertEqual(len(extensions(core, 5, 0)), 30)
        one = extensions(core, 5, 1)
        self.assertEqual(len(one), 360)
        self.assertIn(0xa880888088800000, one)
        self.assertEqual(dual(dual(core, 5), 5), core)
        self.assertEqual(len(extensions(core, 5, 2)), 3780)

    def test_mixed_order(self):
        # Read rows directly, independent of the column and relabel helpers.
        core = 0xe8a8a800
        expected = 0
        for bits in product((0, 1), repeat=7):
            row = sum(bit << i for i, bit in enumerate(bits))
            old = sum(bits[i] << j for j, i in enumerate((6, 4, 5, 2, 1)))
            expected |= ((((core >> old) & 1) | bits[3]) & bits[0]) << row
        self.assertIn(expected, extensions(core, 5, 2))
        self.assertEqual(relabel(core, 5, tuple(range(5))), core)


if __name__ == "__main__":
    unittest.main()
