# First-gate symmetry for L-meta-9742

The graph has 14 orbits on the 325 unordered pairs of distinct input variables. A search for a normalized monotone circuit can therefore fix its first binary gate to one of **28 choices**, one AND and one OR for each representative below.

| Input pair | Orbit size | Graph edge |
| --- | ---: | --- |
| (0, 1) | 6 | no |
| (0, 2) | 18 | no |
| (0, 13) | 1 | no |
| (0, 14) | 18 | no |
| (0, 17) | 6 | yes |
| (1, 2) | 54 | no |
| (1, 3) | 6 | no |
| (1, 14) | 18 | yes |
| (1, 15) | 36 | no |
| (1, 17) | 9 | no |
| (2, 4) | 54 | no |
| (2, 8) | 18 | no |
| (2, 14) | 27 | yes |
| (2, 16) | 54 | no |

## Why these are the full graph orbits

The script reads the 51 edges from the assignment. The graph is connected and bipartite, so every graph automorphism preserves both parts or exchanges them. The degree-three vertices are point 0 and line 13. Every automorphism preserves their unordered pair, so adding the missing edge (0, 13) extends that automorphism to the completed incidence graph.

For a part-preserving automorphism, point 0 and line 13 are individually fixed. In the completed graph, two distinct points determine a unique common line and two distinct lines determine a unique common point. Starting from the four points (0, 1, 2, 5), repeated joins and meets recover the remaining 22 labels. The JSON records the steps as triples (u, v, w), where w is the unique common neighbor of u and v in the completed graph. Thus the images of these four points determine the entire map. The enumeration tries every ordered triple of distinct nonzero point images for (1, 2, 5) in which the image of 1 lies on line 13. It executes the same joins and meets and keeps every bijection preserving the original 51 edges. This recovers all 108 part-preserving automorphisms.

Number a line by its label 13+j. The involution sending point i to line 13+((-i) mod 13) and line 13+j to point (-j) mod 13 preserves the edge set. Composing it with each of the 108 maps enumerates all part-exchanging automorphisms, since composing any part-exchanging automorphism with this involution gives a part-preserving one. The script checks all 216 permutations, closure under composition, orbit disjointness, orbit sizes by the orbit-stabilizer identity, and pair and edge coverage.

## Why the circuit reduction preserves size-bounded feasibility

Prune unused gates, bypass a gate with repeated inputs by idempotence, and propagate any constants using the AND and OR identities. Unary identity gates can likewise be bypassed and empty AND or OR gates evaluated as constants if the circuit representation admits them. These rewrites preserve the function and can only decrease gate count. The edge function has value zero on every singleton and value one on every listed edge, so it is neither a constant nor a single variable. A normalized circuit computing it therefore has a first binary gate in topological order, with two distinct variables as inputs.

Let that gate have operation T and input pair P. Some graph automorphism g sends P to its orbit representative R. Rename every input i throughout the circuit to g(i). Every graph edge maps to a graph edge, so the renamed circuit computes the same edge function with the same gate count and now starts with T on R. Commutativity permits either input order. Conversely every circuit found in a representative case is a circuit for the original task. The orbit computation preserves both gate labels for every representative.

The 28 labeled orbits form a complete first-gate case split. A separate minimum-size argument eliminates the 11 nonedge AND cases from the size-bounded decision. See `solver/README.md` for the proof and the 17 retained case IDs.

## Reproduce

Use Python 3 and the standard library. With the public assignment named `assignment.json` beside the script, run the command below. An explicit assignment path is also accepted.

```sh
python3 first_gate_symmetry.py > regenerated.json
cmp regenerated.json first_gate_orbits.json
```
