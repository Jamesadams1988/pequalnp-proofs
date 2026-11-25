# Two restricted 52-line strategies for PHP(4,3)

The four-pigeon, three-hole formula has a 52-line cutting-planes refutation. The two restrictions below each require all 52 lines. A 51-line derivation could still use intermediate inequalities across holes in ways that these restrictions exclude. The checked unrestricted lower bound in L-meta-9672 is 49. A line represents an integer inequality with `≥` orientation. Addition, nonnegative integer multiplication and division with a ceiling on the right each cost one line. [Cutting-planes definitions](https://github.com/open-goat/pequalnp-proofs/blob/08fca175c9ee19441e2922bb575ae124b47da90d/lean/PEqualNP/Defs/SearchCP.lean) · [Unrestricted lower bound](https://github.com/open-goat/pequalnp-proofs/pull/16368) · [51-line question](https://data.pequalnp.com/data/lemma/L-meta-9682.549ce929eed1.json)

## Finishing with one hole

First derive the capacities of two holes. In each hole add the three pair inequalities on a triangle and divide by two. Double the result, add the three pair inequalities incident to the fourth pigeon, and divide by three. This costs 14 lines per hole, including the six pair premises. Seven more lines sum the four pigeon premises, and two additions give `x0+x1+x2+x3 ≥ 2` in the final hole. The prefix therefore costs 37 lines.

Suppose the continuation uses only this last total and the six pair premises of the final hole. With those seven premises counted, an optimal refutation has **16 lines**. For an upper bound, the triangle on `x0,x1,x2` gives `x3 ≥ 1` after summing, dividing by two, and adding the total. Adding the same total to the three summed pairs incident to `x3`, then dividing by two, gives `x3 ≤ 0`. Add the two bounds. Since the prefix already supplies the total, this continuation contributes 15 new lines.

All seven premises are necessary. Removing the total admits the zero assignment. Removing a pair admits the assignment setting just its two endpoints to one. In a derivation trimmed to ancestors of the contradiction, the line count is `2A−1+U+R`, where `A` counts sources, `U` counts unary steps and `R` counts uses of nonfinal lines beyond their first. This follows by counting edges from parents and children. Some division must occur because the all-half point satisfies all axioms. Hence at most 15 lines forces seven sources and `U+R ≤ 2`.

A tree using the seven premises once cannot derive the contradiction, even with arbitrarily many legal divisions. `Residual.lean` verifies this by induction using a closed catalog of 246 pairs of a premise mask and a line. A remaining candidate must have one division and either a scalar multiplication or one shared line. Every premise is tight at the all-half point. A single effective division creates violation exactly one half there. The final contradiction has violation one, so the divided line must be doubled downstream. The second Lean theorem excludes every doubling of a read-once subexpression followed by addition of the untouched premises. The graph count and violation argument are given here in prose. The finite assertions are `FinalHole.noFalse` and `FinalHole.noDouble`. [Lean certificate](Residual.lean)

## Mixed triangle choices

In each hole choose one excluded pigeon. Sum and round the triangle on the other three to obtain `Q`, and sum the three pairs incident to the excluded pigeon to obtain `R`. The three columns plus the four pigeon premises take 37 lines. Assume at least two distinct pigeons are excluded, and that above these ten premises each is used once. Up to renaming, the excluded-pigeon patterns are `001` and `012`.

Each premise is necessary. Removing `Q` permits two nonexcluded pigeons in its hole. Removing `R` permits the excluded pigeon and one other in that hole. Removing a pigeon premise lets the other three occupy distinct holes. A tree consequently uses nine additions, leaving at most five unary steps in a 51-line attempt. The ten coefficient vectors have a one-dimensional kernel, spanned by weights two on each `Q`, one on each `R`, and three on each pigeon premise. Thus, at each internal node, the sum of its weighted premise vectors fixes its coefficient vector up to positive scale.

`ray_relax.py` enumerates every binary partition and unary-budget allocation. It stores an integer right-side bound for each fixed scale and a normalized upper bound covering arbitrary positive scales. If the weighted vector has coefficient gcd `g` and normalized bound `B`, division rounding at output scale `μ/g` gives a new normalized bound at most `(g/μ) ceil(μ B/g) ≤ g ceil(B/g)` for every positive integer `μ`. Both exclusion patterns give root bounds at five unary steps of `0` at fixed scale and `−1` at arbitrary scale. Neither yields a positive constant contradiction. At six steps the fixed bound reaches one, attained by doubling each `Q` and dividing `2Q+R` by three in each hole. This restricted result uses exact rational arithmetic and a SymPy kernel computation. [Enumerator](tools/ray_relax.py)

## Replay

Run from this directory with Python 3.10 or newer. The mixed-triangle enumeration also requires SymPy. For the Lean check, load the repository’s Lean 4.36.0 and Mathlib environment.

```sh
python3 -B tools/final_hole.py
python3 -B tools/local_audit.py
python3 -B tools/ray_relax.py 001 6
python3 -B tools/ray_relax.py 012 6
python3 -B tools/make_residual.py | cmp - Residual.lean
lean -j1 Residual.lean
```

The direct residual checker verifies the 16-line witness and excludes 123 doubled, four disjoint-cut and three nested-cut configurations. The independent audit checks exact coefficient states and solves the possible scalar-multiplier equations over the rationals. The generator reproduces the Lean file byte for byte, and both exported exclusion theorems report `propext`, `Classical.choice` and `Quot.sound`.
