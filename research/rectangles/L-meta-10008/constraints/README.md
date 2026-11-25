# Row differences and three-rectangle neighborhoods

For a row $p$, let its signature be the set of rectangles containing $p$
on the row side. In any sound cover, if exactly one rectangle $R$ belongs
to the signature of $p$ but not that of $q$, every row of $R$ is on
the common projective line through $p,q$. To see this, take a row $x$
of $R$ off that line. The line $qx$ misses $p$. A rectangle covering
the zero at $(p,qx)$ must omit $q$, so must be $R$. That is impossible
because $x$ lies on $qx$.

A rectangle with collinear row support has area at most 45. For $k>0$
rows on one line, their union of incident lines has size $1+5k$, leaving
$30-5k$ candidate columns. The product $k$30-5k$$ peaks at 45.
Consequently, if every rectangle has area at least 46, each ordered row pair
has at least two distinct rectangles containing the first row and omitting
the second. The same holds for columns. In particular at a row with
signature of size three, each pair of those rectangle indices belongs to
that row alone.

`PencilDifference.lean` formalizes the unique-difference theorem for any
Boolean relation on 31 points with the unique joining line property. It
derives the two-difference conclusion given the incidence and collinear-area
bounds, and it checks row separation for the literal matrix and its transpose.
The standalone C++ replay verifies the remaining hypotheses in both orientations
by counting every pairwise intersection and testing the subsets of each line.
Run `lake env lean /absolute/path/to/PencilDifference.lean`
from the upstream Lean project.

## Pure six-by-ten covers

Through a fixed row $p$, there are 600 sound rectangles with exactly six
rows and ten columns. Among their unordered triples, exactly 4,600 cover
all 25 zeros of $p$. The three row supports meet pairwise only at $p$.
The census gives the following counts.

| Sorted sizes | Covering triples | Partner pairs per fixed first rectangle |
| --- | ---: | ---: |
| 2, 2, 2 | 4,000 | 20 |
| 0, 0, 5 | 600 | 3 |

The C++ census enumerates the other five rows among the remaining 30,
checks that at most ten columns are available in each case, then enumerates
all unordered triples of the eligible rectangles. It checks the partner
counts individually for each of the 600 rectangles. A simultaneous cyclic
shift preserves the literal entries, so this census applies at each row.

A cover using only six-by-ten rectangles needs at least three through every
row. Seventeen rectangles have 102 row memberships, leaving nine above
the minimum of 93. At least 22 rows therefore obey the triple restriction.
For sixteen rectangles the corresponding count is at least 28. The shape
restriction is necessary for these counts.

Run the standalone census with a C++20 compiler.

```sh
g++ -std=c++20 -O2 ConicTriples.cpp -o ./conic-triples
./conic-triples
```
