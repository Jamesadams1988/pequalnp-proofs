# Independent Hall frontier check

For the pigeon and hole expansions used in the mixed Hall construction, the smallest possible numbers of distinct required nodes at hole levels 1, 2 and 3 are respectively **4, 6 and 4**. This checker tests each possible smaller set directly. The mixed Hall argument supplies the two rules and the per-node costs. [Macro definitions and proof](../mixed-hall/README.md)

A node is a pair of subsets of the five pigeons and four holes. A node at level k has k+1 pigeons and k holes. A pigeon expansion chooses one pigeon and requires all k children formed by dropping it and one of the holes. A hole expansion chooses one hole and requires all k+1 children formed by dropping it and one of the pigeons. To test a proposed set at one level, the program marks a node at the next level available precisely when all children of at least one expansion are available. This gives the exact closure under the two rules, allowing unbounded sharing. Availability increases when a node is added, so checking all sets one below the proposed minimum excludes every smaller set.

| Hole level | Nodes at that level | Size tested | Sets tested | Sets reaching the root |
| --- | ---: | ---: | ---: | ---: |
| 1 | 40 | 3 | 9,880 | 0 |
| 2 | 60 | 5 | 5,461,512 | 0 |
| 3 | 20 | 3 | 1,140 | 0 |

At each level the checker also verifies a positive control of size 4, 6 or 4 using a fixed pigeon subset and every hole subset of that level. Compile and run from this directory with a C++20 compiler.

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror cut_check.cpp -o cut_check
./cut_check
```

## Recovering node ownership from an intermediate clause

Distinct expanded nodes have disjoint sets of newly derived clauses. This also follows from the literal sets themselves. Write P and S for the node's pigeons and holes and O for the holes outside S.

A conditional intermediate has exactly one negative literal, for pigeon q and hole h. The holes carrying positive literals outside h are exactly O. If O is nonempty, those literals occupy exactly the rows in P other than q, which recovers P. If O is empty this is the root.

For a positive accumulator with O nonempty, the occupied rows are exactly P. The intersection of the occupied hole sets in these rows is O. In a pigeon expansion the extra literals are confined to its chosen row. In a hole expansion they are confined to its chosen hole and omit at least the anchor row. Thus the number of occupied rows plus the size of their common hole set is five. At the root the accumulator after its first resolution has at most three literals in a single row or column. For each nonempty such clause the corresponding sum is at most four. The empty clause belongs to the root. This recovers P and S from any accumulator and distinguishes it from the conditional clauses.

The fixed-order trace attains the 157-line total from these frontier sizes and the k(k+1) distinct fresh lines per expansion. Ordinary resolution also allows derivations beyond these two expansions. [Kernel-checked witness](../witness/README.md)

## Cheaper recursive hole expansions

The same global minimum holds when each hole expansion with k+1 pigeons may use the recursive column refutation. This version costs 2, 5, 9 or 14 derived lines at levels 1, 2, 3 or 4, and uses all k+1 child Hall clauses. A pigeon expansion retains its costs of 2, 6, 12 or 20. [Column construction](../elimination/README.md)

The clause ownership argument above still applies. Let R be the active pigeon set in a recursive call using hole h. To handle one active pigeon r, the proof takes the original child missing r and resolves away the other active pigeons in h using collisions. Every signed intermediate is a conditional of the form already covered. Solving the call with at least two active pigeons gives P × O together with the positive literals for rows outside R in column h. There are at most k−1 such rows, so the result is one of the positive hole accumulators covered above. With one active pigeon the call uses its original child directly.

The weighted replay enumerates the expansions for all required nodes at a level, forms the union of their child sets and then descends. It discards a partial selection only when its cost, plus the cheapest possible remaining expansions, reaches the current upper cutoff. The disjointness argument makes the sum of node costs exact for this family. The preceding frontier check supplies the lower bounds of four required nodes at level 1 and six at level 2. Symmetry allows the first pigeon or first hole to represent its entire root orientation.

| Root orientation | Minimum resolutions | Total with 45 axioms | Search calls |
| --- | ---: | ---: | ---: |
| Pigeon | 112 | 157 | 4,716 |
| Hole | 129 | 174 | 30,807 |

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror weighted_replay.cpp -o weighted_replay
./weighted_replay
```

The optimal hole-root policy also has a concrete ordinary-resolution trace with 45 axioms and 129 resolution lines. From this directory, run `python3 -B ../tree/formal/verify_tree.py hole-root174.json` to check all parents and pivots. The same Lean generator used for the pigeon-root proof can produce a formal proof with the option `--budget 174`. [Hole-root trace](hole-root174.json) · [Lean generator](../witness/emit.py)
