# Contextual rewrites of the 114-gate star cover

For the literal L-meta-9802 graph, the search found no one-gate saving in **35,744** connected windows of up to four gates. Its starting points are 64 concrete 114-gate formulas. The 95 edges are listed in `edges.txt`, with left vertices 0–19 and right vertices 20–39. The unrestricted 113-gate question remains open.

Run the four canonical layouts or the full experiment with Python 3 and a C++20 compiler. The script creates its binary in a temporary directory and requires no network access.

```sh
python3 replay.py
python3 replay.py --full
```

| Layouts | One-gate windows | Two | Three | Four | Total |
|---|---:|---:|---:|---:|---:|
| Four canonical layouts | 456 | 452 | 560 | 766 | 2,234 |
| All 64 layouts | 7,296 | 7,232 | 8,960 | 12,256 | 35,744 |

Each formula uses one bipartition as the star centers. It combines neighborhood and output disjunctions using balanced or skewed trees. For each orientation and shape, the full run checks the listed ordering and 15 seeded shuffles, using `std::mt19937` and `std::shuffle`. Seeded orderings follow the standard-library implementation. Replay counts above use GNU libstdc++.

For each gate the search enumerates every connected upstream window of one to four gates with a single retained output. A replacement may borrow primary inputs and gates anywhere else in the formula, except the removed gates and consumers of the window output. Independent borrowed wires may be reordered topologically. The search tests direct wires, binary gates, chains, and two single-gate arms combined at the root, up to one fewer gate than the removed window. Constants can be propagated through any nonconstant candidate. Every tested window has both positive and negative required outputs. A three-gate circuit that reuses a gate output simplifies to a formula of no greater size by idempotence or absorption.

The executable constructs all 95 minimal true inputs and all 16,870 maximal false inputs. For a point subset A the unique possible maximal partner on the line side is the complement of its neighborhood. The reverse maximality test checks that every omitted point has a neighbor in that partner. The original 114-gate formula is checked on this complete boundary. Along the path from a window to the output, a sibling must be false at an OR or true at an AND for the replacement value to matter. The resulting positive and negative rows suffice because the complete replacement circuit is monotone. Source signals with identical signatures on these rows are interchangeable.

The replay includes two positive controls. On a disjoint union of ten four-cycles, it finds a genuine gate bypass by borrowing another neighborhood wire. On all 16 assignments of four variables, it rejects two gates and finds three for `(a AND b) OR (c AND d)`, exercising the balanced replacement case.
