# Rectangle search for L-meta-10008

`partial20.json` stores the matrix from the assigned statement, 20 all-zero rectangles, and their uncovered zero entries. It is an incomplete candidate. Coordinates are zero-based and bit `j` in a row mask corresponds to column `j`. Each rectangle is given by its row mask followed by its column mask.

Run from this directory with Python 3.10 or later.

```sh
python3 rectangles.py verify
python3 rectangles.py enumerate
python3 search.py --count 17 --steps 1000 --seed 1 --output candidate.json
python3 rectangles.py --input candidate.json verify
```

Verification inspects every cell. Pass `verify --require-cover` to receive a nonzero exit status for an incomplete candidate. Enumeration closes all intersections of zero neighborhoods. It finds 1,565,748 nonempty maximal rectangles, including 6,200 with the maximum area of 60. Use `enumerate --emit masks.txt` to write the maximal rectangles as decimal mask pairs, one per line.

The search picks an uncovered zero and changes one rectangle to include it. It tries both orders for extending the new rectangle to a maximal one and retains the best partial cover visited. The specified seed makes the run repeatable. A count of 17 targets the assignment threshold. A search that ends with uncovered cells gives no lower bound on the cover number.

The [diagonal torus verifier](torus/) checks a restricted lower bound for covers invariant under a specified group of collineations. The unrestricted 17-rectangle question remains open in this investigation.
