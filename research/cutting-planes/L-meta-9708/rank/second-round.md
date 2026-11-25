# The all-fifths point survives two global rounding rounds

Let $P$ be the ordinary pigeonhole relaxation with six rows, five columns, the
Boolean bounds, each row sum at least one, and each pair in a column summing
to at most one. For a polytope $Q$, its first Chvátal–Gomory closure retains
the points satisfying every integer-objective inequality
$a x \le \lfloor\max_{y\in Q}a y\rfloor$. Write $P_1$ and $P_2$ for the first
and second closures. Then the point with every entry $1/5$ belongs to $P_2$.

## Rank-one witness points

For any independent choice of three distinct holes in each row, put $1/3$
on each of the chosen cells and zero elsewhere. This point belongs to $P_1$
by the earlier theorem `PHPTriples.fullRound`. It allows the three holes to
vary by row. [Prior Lean theorem](https://github.com/Jamesadams1988/pequalnp-proofs/blob/ca052f3f52b8d4bd947fbb6979a7b37e9e2fc02d/research/cutting-planes/L-meta-9682/TripleSupport.lean)

We may also pin one row $i$ to a single hole $h$, and put thirds on any
three of the other four holes independently in each remaining row. To
verify this, embed the five-row, four-hole relaxation into $P$ by adjoining
the unit row and a zero in column $h$ in every remaining row. The embedding
preserves every initial constraint, has integer linear part, and adds an
integer constant vector. An integer objective on the full LP pulls back
to an integer objective plus an integer constant. Its rounded upper bound
on the embedded relaxation is at most the rounded upper bound on $P$.
The earlier theorem on the five-row, four-hole relaxation therefore places
every pinned witness in $P_1$.

## Every second-round cut

Fix an arbitrary integer objective $a$. All the witnesses just described
and the all-fifths point have row sums exactly one. Subtract each row
minimum from the entries of that row. The objective value changes by the
same integer on every point used in the comparison, so rounding commutes
with this change. Write $r$ for the resulting nonnegative integer array
and $S$ for its sum. Every row of $r$ has a zero. It suffices to show that
some rank-one witness has normalized objective at least $\lceil S/5\rceil$.

Choose the three largest entries in each row. They carry at least three
quarters of its normalized weight, because there are at most four positive
entries. The resulting rank-one witness has objective at least
$\lceil3S/4\rceil/3$. Let $B$ be the floor of the largest normalized
objective across the ordinary and pinned witnesses. These witnesses have
denominator three, so their objective numerators are at most $3B+2$.
It follows that $3S\le4(3B+2)$.

Suppose $S>5B$. The preceding inequality yields $B\le1$. Pinning a cell
of weight $w$ gives objective at least $w$, so $B=0$ forces $S=0$.
For $B=1$, the same pinning argument makes every weight zero or one,
and the two inequalities on $S$ force $S=6$. If every row has at most
three ones, ordinary rowwise triples cover all six and give objective two.
Otherwise some row has four ones. Pin a one in another row. At least three
of the four ones remain outside the pinned hole, giving another unit of
objective on top of the pinned unit. In each case an admissible rank-one
witness attains two, contradicting $B=1$.

Thus $S/5\le B$, as required. This argument allows arbitrary integer
objectives mixing holes and includes both Boolean bounds. Since the point
also belongs to $P_1$ by averaging ordinary triple witnesses, it survives
every rank-two cut and their nonnegative linear combinations.

The second-round five-pigeon clique capacities force the surviving point
to be unique. Summing the six such capacities in a column, then dividing by
five, yields its six-pigeon capacity in round three. Summing all five
column capacities contradicts the six pigeon rows. This proves exact
rounding depth three. The unrestricted number of inference lines is a
separate question.

[Lean proof of the uniform-coordinate conclusion from the five-pigeon cuts](Singleton.lean)

The [integer-objective lemma](UniformFifths.lean) handles arbitrary signed coefficients, a positive divisor and the finite ordinary and pinned witnesses. The membership of the witnesses in the first closure follows from the earlier theorem and the affine embedding above. On any five-pigeon subset of one hole, the ten triangle bounds from round one sum to six times its occupancy at most ten. Dividing by six in round two gives the five-pigeon capacity of one.
