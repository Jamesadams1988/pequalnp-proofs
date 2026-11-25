# Six-input circuit and formula minima

The assigned table is `0xfeeaeeeafeeaeaaa`, with input zero the low bit of the row number. Its two coordinate-zero faces are `0xe8a8e880` and constant true. Both circuit minima are **nine gates**. Both formula minima are **ten literal leaves** when a negated input counts as a single leaf.

## Circuit replay

Run `python3 circuit_check.py` with Python 3 and a C++20 compiler. It builds the unchanged enumerator from `L-meta-13646/test/search.cpp` in a temporary directory. It excludes the core at unrestricted gate budgets four through seven and checks two nine-gate monotone witnesses at all 64 rows. One witness extends the shared eight-gate core in `PEqualNP.Outside.L_meta_8642.witness`. An independent, unshared witness is

```
(x0 | (((x4 | x5) & x1) & (x2 | x3))) | ((x3 & x2) & (x1 | x4))
```

The enumerator generates binary AND/OR and unary NOT. For a minimum circuit on essential inputs one can remove dead gates, fold constants, bypass unary AND/OR, and remove a wire whose table already exists. A connected circuit on five essential inputs needs at least four binary gates. Every input and every non-final gate in a minimum circuit has a consumer. With `r` gates left, there are at most `r+1` signals which still need a consumer, since a binary gate can reduce the count by at most one. Finally, adjacent independent gates can be ordered by operand indices and operator in a lexicographically least topological order. These facts justify the search reductions used by the original enumerator.

The false face is nonconstant and coordinate zero is essential at input row zero. Applying `PEqualNP.Outside.L_meta_4795_aux.one_gate_at` and relabeling to remove the pinned coordinate yields a five-input circuit with at least one fewer gate than any six-input circuit. The upper and lower bounds therefore meet at nine.

## Separate formula replay

Run `python3 formula_check.py`. For each pair of nonempty positive and negative row sets, the program computes the minimum leaves in a formula separating them. It first tests literal leaves. An OR can partition the positive set between its children and an AND can partition the negative set. If one child handles all the rows of the split set, that child alone is a smaller separator, so the recurrence only needs nontrivial splits. Conversely, combining two separators for any such split gives a separator. The dynamic program's minimum on the given sample is consequently a lower bound for any formula matching the whole table. The witnesses attain that bound and are checked against every row. The script computes both the positive-only and arbitrary-signed-literal versions.
