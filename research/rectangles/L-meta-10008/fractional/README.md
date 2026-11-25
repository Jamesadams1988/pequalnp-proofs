# The exact fractional cover costs 155/12

Allow each zero rectangle a nonnegative real weight and demand total weight at least one on each zero cell. For the 31-by-31 matrix the minimum total weight is **155/12**. This explains the limit of any lower bound that gives nonnegative weights to individual zero cells and bounds the weight of a single rectangle.

The matrix has 775 zeros. A checked upstream result bounds every zero rectangle by 60 cells, so summing cell demands gives 775/60. Enumerating all six-point row sets gives 3,100 that avoid exactly ten columns. Each zero cell occurs in exactly 240 of their 6-by-10 rectangles. Giving every one of them weight 1/240 reaches the lower bound. [Upstream area bound](https://github.com/open-goat/pequalnp-proofs/blob/41fe834b000fc5190f11224bb9e6bc645249cc7b/lean/PEqualNP/Outside/L_meta_10004.lean) · [Enumeration](fractional.py)

A smaller certificate uses 17 base rectangles and their 31 simultaneous cyclic translates. According to the stored integer multiplicities these give 620 rectangle occurrences. Every zero is covered exactly 48 times and every one is covered zero times. Dividing every multiplicity by 48 gives the same optimum. Lean checks the cyclic structure of the literal matrix, the counts at every displacement and the total weight. A separate Python replay expands the translates and checks every cell directly. [Sparse certificate](sparse.json) · [Kernel checks](Fractional.lean) · [Direct expansion](check_sparse.py)

Five full shift orbits of 6-by-10 rectangles would have enough area for exactly twelve copies of the zero matrix. A meet-in-the-middle enumeration excludes all choices of five orbits, including repetitions. There are 100 such orbits. This last calculation concerns that specific proposed multicover. [Enumeration](cyclic_balance.py)

Run `python3 -B fractional.py`, `python3 -B check_sparse.py`, and `python3 -B cyclic_balance.py` in this directory. With the pinned Lean project built, run `lake env lean /path/to/Fractional.lean` from its `lean` directory.
