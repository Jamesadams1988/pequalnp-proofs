# An unrestricted 40-gate lower bound for L-meta-9742

Research credit belongs to James Adams. Every monotone circuit of fan-in at most two computing the specified 51-edge function has at least **40 gates**. If its first gate in a gate-minimum representation is an AND, the same calculation gives **41**. The proof combines gate reductions with a five-round finite calculation. Python and C++ independently reproduce the finite calculation. The leaf theorem L-meta-614 is verified upstream in Lean.

## Choosing the first gate

Work with a minimum circuit for the induced graph, on the vertices incident to an edge. An isolated input can be pinned to false without affecting the function, and input renumbering costs no gates. Remove dead gates, propagate constants and bypass copies and repeated-input gates. Native reads outside the evaluated prefix give false. Every remaining gate is binary, has two different operands, and lies in the output cone. For a graph on at least three active vertices the first gate g is not the output, since all active vertices are essential. Its two inputs x,y are raw vertices.

If g is an AND on a nonedge, replace it by false. This preserves its value on all minimal true inputs and can only decrease other values. Monotonicity then gives the same function on the whole cube. The replacement saves a gate. Similarly, OR(x,y) can be replaced by y if x's only neighbor is y, since every minimal true input containing x also contains y. These choices are absent from a minimum circuit.

## Savings from a second reader

Fix either endpoint x. Its absorbing bit makes g constant and its neutral bit makes g a copy of y. The neutral bit saves at least one gate. The absorbing bit saves at least two, since a direct consumer of g can also be eliminated. If the original edge function remains dependent on x after setting y to g's absorbing bit, then x has another direct reader h. Otherwise setting y to that bit would hide every occurrence of x. For AND, this dependence holds when x has a neighbor other than y. For OR, it holds when x and y are adjacent or x has a neighbor outside y's neighborhood.

The other operand of h cannot be g. Both AND(x,g) and OR(x,g) simplify to x or g by absorption. Consequently h is distinct from every direct consumer of g. The neutral pin now removes g and h. The absorbing pin removes g, h, and a direct consumer of g.

Suppose both x-cofactors are nonconstant. Then neither g nor h is the output, because a gate directly reading x is constant at its absorbing bit. If h has the opposite operation to g, either pin makes one of the two gates constant, and the constant gate has a distinct direct consumer. Both pins save at least three gates. If h has the same operation as g, the neutral pin saves at least two and the absorbing pin saves at least four. Indeed g and h then both become constant. Their sets of direct consumers have at least two members in union. Otherwise both feed their sole common consumer k; if g = x ⋆ y and h = x ⋆ z, the three-gate fragment k(x ⋆ y, x ⋆ z) equals x ⋆ k(y,z) for either choice of k and ⋆ in {AND,OR}. Since g and h have no other users, this gives a smaller circuit. Construct the replacement at k's original position, where y and z are already available. This argument also shows h cannot depend indirectly on g in the sole-common-consumer case, by acyclicity.

Let A,N be lower bounds on the absorbing and neutral cofactors respectively. Under the stronger hypothesis the endpoint consequently gives at least

    min(max(A+3,N+3), max(A+4,N+2)).

Take the maximum over the two endpoints for each possible first gate and the minimum over first-gate choices.

## Cofactors and terminal bound

Pinning x to zero deletes x. Pinning x to one gives the OR of its d neighbors as individual variables and the edge predicate of the remaining induced graph outside x and its neighbors. If that graph has an edge, setting each of the d OR variables to false saves at least one gate per variable: each is essential and its direct reader becomes a copy or constant. Thus the cofactor costs at least d plus the lower bound for the remaining graph. If the graph has no edge, the cofactor is OR of d variables and has exact cost d−1. Positive degree guarantees d≥1. Constant false itself costs zero in the native model through an invalid output. With at least three active vertices, setting any single vertex to either bit also saves at least one gate of the original circuit. These bounds hold for general monotone circuits with shared gates.

At a terminal state L-meta-614 gives n+t−1, where n is the number of active vertices and t is the minimum size of a vertex cover of edges whose endpoints both have degree at least two in the current graph. The program checks that nonadjacent vertices of degree at least two have different neighborhoods and that each eligible edge admits the required alternative neighbor pair. All graphs are induced subgraphs of the bipartite input. The size of a maximum matching in the eligible-edge subgraph equals t by Kőnig's theorem; even an individually verified matching gives the needed lower bound on t. The one-edge case has cost one.

## Replay

From the directory containing `assignment.json`, run these commands in Bash with Python 3.10 or newer and a C++20 compiler. Both programs check the 51 labeled edges against the assignment before evaluating the bounds. Python represents induced graphs by surviving vertices and finds a matching in each terminal graph. C++ represents each graph by surviving edges and computes the minimum vertex-cover size by branching.

```bash
set -euo pipefail
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 -B restrictions/game.py --assignment assignment.json --rounds 5 > "$work/python.txt"
diff -u restrictions/expected.txt "$work/python.txt"
c++ -O3 -std=c++20 restrictions/independent.cpp -o "$work/independent"
"$work/independent" 5 assignment.json > "$work/cpp.txt"
diff -u restrictions/independent-expected.txt "$work/cpp.txt"
```

Both diffs are empty on a successful replay. The successive bounds through five rounds are 38, 38, 38, 39, 39, and 40. At five rounds all 51 possible first ANDs give 41 and all 325 possible first ORs give 40. The terminal bound is evaluated on 594,160 different induced subgraphs. This covers unordered pairs of distinct active inputs. Constants, repetitions, unused gates and unary gates were eliminated by taking a minimum circuit. The unrestricted 63-gate claim remains open.
