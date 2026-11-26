# A gate bound for safe conjunction blocks

A block is a conjunction of OR clauses over raw point and line variables. It is *safe* if every assignment that satisfies it contains an incident pair. The OR clauses may share subcircuits, and the conjunction gates may have fanout. Write `H` for the incident pairs that satisfy the block when only their two endpoints are selected. The block can also accept larger assignments that contain no pair from `H`.

Let `U` consist of `t` points, each incident to more than `r` accepted lines of `H`. No two points have two common lines. The block requires at least

\[
\sum_{i=0}^r {t\choose i}
\]

distinct clause signals, and hence at least one fewer binary AND gates. The same claim holds with the sides reversed. The theorem `factors` uses the cardinality of the family of all subsets of `U` of size at most `r`; `upToTwo` evaluates it at `r=2`.

For each such subset `S`, select `S` and all lines avoiding `S`. This input contains no incidence, so at least one clause rejects it. If `S` and `T` differ, exchange them if necessary and take `p` in `S` outside `T`. Each point of `T` rules out at most one line through `p`. Some accepted line through `p` therefore avoids `T`. A clause rejecting both inputs would contain neither `p` nor that line, contradicting its acceptance on this two-variable input. This makes the choice of a rejecting clause injective. Backwards expansion of one binary AND increases the number of frontier wires by at most one, including when its inputs or ancestors are shared.

## Block replacement

Suppose all active rows of `H` have degrees between 3 and `m`, inclusive, and at least `2m+1` rows are active. Then the block's conjunction gates alone cost at least `|H|+t`. Indeed its frontier has at least `1+t+binom(t,2)` clauses, and `binom(t,2) ≥ tm ≥ |H|`. A row-star circuit for `H` costs `|H|+t−1` gates and reads the endpoints of each accepted pair once.

If this block is one disjunct of a circuit computing incidence, it can be replaced by its accepted row stars whenever its conjunction gates are private to it. The identical literal pair witnesses show correctness on all inputs. For any selected incidence, examine the input containing only its two endpoints. If the other disjuncts accept there, monotonicity makes them accept the full input. Otherwise the new stars accept the pair. Both the other disjuncts and the new stars are safe. External reuse of the block's gates affects the cost of deleting it. `denseBlock` proves the gate charge, and `replaceAtTop` proves the semantic replacement.

## Whole-plane consequence

For a single such block computing all incidences of a plane in the assignment, the lines form `N` active rows with degree `q+1`. The projective-plane axioms imply that two lines have at most one common point. Taking `r=2` gives at least `1+N+binom(N,2) ≥ N(q+2)+1` clause signals. Thus even the AND layer needs at least `N(q+2)` gates. The existing read-one star construction uses `N(q+2)−1` gates. This excludes an entire AND-over-OR circuit from being a sub-star-budget counterexample. General alternating circuits and blocks sharing conjunction gates with other disjuncts remain outside this replacement argument.

`FactorCount.lean` checks the counting lemmas and replacement implication in Lean. The gate semantics use a binary conjunction DAG over a frontier of OR clauses, with the final conjunction listed first for backwards expansion. The file imports Mathlib and can be replayed directly with the upstream project's Lean environment.

```sh
lake env lean /path/to/FactorCount.lean
```
