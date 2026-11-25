# How many leaves does it take to find a collision?

Five labeled pigeons each choose one of four holes. A correct leaf names two pigeons forced into the same hole. A query may test membership of one pigeon's hole in a subset of the four labels. The minimum number of leaves in an adaptive search tree is **120**, even when every such subset is available. Testing just the two bits of a hole label attains 120 leaves. A full binary tree with 120 leaves has 239 nodes.

## Exact tree calculation

The state is the list of five remaining hole domains. Independent answers leave a Cartesian product. Two pigeons have to coincide on every assignment in that product precisely when their domains are both the same singleton. Such a terminal state costs one leaf. Otherwise, a question gives two smaller nonempty states. For a chosen question their optimal leaf counts add. Minimizing over all questions gives the optimal cost by induction on the total size of the five domains. Sorting the domains only changes the names of the pigeons.

The top-down calculation evaluates raw bit questions, parity questions confined to one pigeon, and arbitrary questions confined to one pigeon. Each model gives 120. The bottom-up replay uses subsets of explicit hole labels, enumerates every bipartition of a domain and checks all 11,628 unordered states. It also gives 120. The independent Lean reduction takes an ordinary resolution proof tree to a raw-bit query tree with at most the original number of leaf occurrences. Combined, these checks require at least 120 axiom-leaf occurrences in such a proof tree. The 149-line witness can reuse earlier lines. Its unrolled tree has 140 leaf occurrences. [Tree reduction](../review/QueryTree.lean)

## A signed lower bound for disjoint partitions

A partition can use arbitrary disjoint product boxes without any query ordering. Every nonempty box must name a pair of pigeons that collide throughout that box. The two corresponding factors must then be the same singleton. If either could take a second value, the other coordinate could stay fixed, giving a counterexample inside the box.

Assign weight +4 to each assignment of occupancy type (2,1,1,1), weight −1 to each of type (2,2,1), and zero to all others. There are 240 assignments of the first type and 360 of the second, giving total weight 600. Relabeling holes and pigeons preserves the equal-pair count and hence the weight. Normalize any box by placing its named pair first and their common hole at 0. If any of the other three pigeons also occupies 0, the assignment has zero weight. The other three factors can therefore be restricted to arbitrary subsets of the three remaining holes. Across all 512 choices, the greatest box weight is 6. Summing over a disjoint cover gives **at least 100 boxes**. A cover with overlaps need not preserve a signed sum. The argument requires every box to name a colliding pair.

Lean checks the 600 total, the 512 local bounds, the zero-weight reduction, and the general summation inequality for disjoint partitions. The relabeling argument above connects normalized boxes to arbitrary labeled boxes. Questions that compare different pigeons can leave non-Cartesian states, and the public desk also allows shared derivations. [Finite Lean checks](SignedBoxes.lean)

## Replay

Use Python 3.10 or newer and run the following from this folder.

```sh
python3 query_dp.py
python3 check_bottom_up.py
python3 check_boxes.py
```

With the upstream Lean 4.36.0 checkout and its dependencies built, run `lake env lean /path/to/SignedBoxes.lean` from its `lean/` directory.
