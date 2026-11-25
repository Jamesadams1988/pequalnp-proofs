import unittest

from match_cofactor import first_match


def table(rows):
    return sum(1 << row for row in rows)


class MatchTests(unittest.TestCase):
    def checked(self, six, five):
        match = first_match(six, five)
        p, b, label = match["pin"], match["value"], match["label"]
        self.assertEqual(label[p], 0)
        self.assertEqual(sorted(label[:p] + label[p + 1:]), list(range(5)))
        # Read each six-input face row back into the reported five-input labeling.
        for x in range(64):
            if (x >> p) & 1 == b:
                y = sum(((x >> i) & 1) << label[i] for i in range(6) if i != p)
                self.assertEqual((six >> x) & 1, (five >> y) & 1)
        x, x_flip = match["essential_rows"]
        self.assertEqual(x ^ x_flip, 1 << p)
        self.assertNotEqual((six >> x) & 1, (six >> x_flip) & 1)
        u, v = match["nonconstant_rows"]
        self.assertEqual(((five >> u) & 1, (five >> v) & 1), (0, 1))
        return p, b, label

    def test_row_8657(self):
        self.assertEqual(self.checked(0xeeeaeaeaeee0e8e0, 0xeaaac880),
                         (2, False, [0, 2, 0, 1, 3, 4]))

    def test_three_cycle(self):
        # A different ordering at coordinates 0..2 produces a different table.
        six = table([32, 36, 37, 39, 47, 63])
        five = table([0, 1, 3, 7, 15, 31])
        self.assertEqual(self.checked(six, five), (5, True, [1, 2, 0, 3, 4, 0]))

    def test_unreachable(self):
        # The dual of row 8657 (0xfeecaaa8) is also unreachable by a permutation.
        for five in (1, 0xfeecaaa8):
            self.assertIsNone(first_match(0xeeeaeaeaeee0e8e0, five))

    def test_ignored_pin(self):
        # Fixing an unused variable retains the projection. Fixing x0 is constant.
        self.assertIsNone(first_match(0xaaaaaaaaaaaaaaaa, 0xaaaaaaaa))

    def test_constants(self):
        for five in (0, 0xffffffff):
            self.assertIsNone(first_match(0xaaaaaaaaaaaaaaaa, five))

    def test_identifications_only(self):
        # Parity of six has five essential inputs on each face. Identifying two
        # free variables cancels them and yields parity of the other three.
        six = table(x for x in range(64) if x.bit_count() % 2)
        five = table(y for y in range(32) if (y & 0xe).bit_count() % 2)
        self.assertIsNone(first_match(six, five))

    def test_range(self):
        for six, five in [(1 << 64, 1), (0, 1 << 32), (-1, 1), (0, -1)]:
            with self.assertRaises(ValueError):
                first_match(six, five)


if __name__ == "__main__":
    unittest.main()
