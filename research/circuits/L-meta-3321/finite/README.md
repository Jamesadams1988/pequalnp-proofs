# Minimum clean circuits through size three

The enumeration covers 1, 2, 15 and 334 labeled four-cycle-free relations at side sizes 0, 1, 2 and 3. It evaluates every upper-bound witness and each of its AND gates on every input. Thirteen lower-bound instances require SAT search, one at size two and twelve at size three. Lean's standard-library LRAT checker accepts the resulting certificates. The circuit-to-CNF argument appears below. The independent Lean proof of the desk conclusion through size three is in [the parent directory](../UpToThree.lean).

## Reproduce

Use Python 3.10 or later, CaDiCaL 2.1.2 and Lean 4.36.0. Run these commands in Bash from this directory. The default size range is 0 through 3. Use `--n 2`, for example, to run one side size. The default SAT timeout is 30 seconds per instance and can be changed with `--timeout`.

```bash
set -e
work=$(mktemp -d)
python3 verify_small.py cadical --output "$work"
files=("$work"/n{2,3}/*.cnf)
test "${#files[@]}" -eq 13
lean --run ReplayFinite.lean "${files[@]%.cnf}"
python3 controls.py cadical --output "$work"
```

Each completed `nN/results.json` holds the witnesses and their lower-bound tests. The positive control finds an eight-gate satisfying assignment for the six-cycle, checks every CNF clause, and evaluates the decoded circuit on all 64 inputs. Two control circuits computing the same one-edge function separately violate the mixed-AND and singleton conditions. An empty AND and a missing output exercise the circuit model's defaults.

## Complete witness table

Bit `N*p+l` in the hexadecimal mask indicates incidence of point `p` and line `l`. The orbit includes independent permutations of the points and lines, and exchange of the two sides. Points occupy wires 0 through N−1, then lines occupy N through 2N−1. Each gate expression creates the next wire, starting at 2N. The symbol `&` denotes AND and `∨` denotes OR. A missing output reads false. Each reported minimum equals the number of gate expressions.

| N | Mask | Orbit | Minimum | Output | Successive gates |
|---:|---:|---:|---:|---:|---|
| 0 | 0x0 | 1 | 0 | 0 | ∅ |
| 1 | 0x0 | 1 | 0 | 2 | ∅ |
| 1 | 0x1 | 1 | 1 | 2 | 0&1 |
| 2 | 0x0 | 1 | 0 | 4 | ∅ |
| 2 | 0x1 | 4 | 1 | 4 | 0&2 |
| 2 | 0x3 | 4 | 2 | 5 | 2∨3, 0&4 |
| 2 | 0x6 | 2 | 3 | 6 | 0&3, 1&2, 4∨5 |
| 2 | 0x7 | 4 | 4 | 7 | 2∨3, 0&4, 1&2, 5∨6 |
| 3 | 0x0 | 1 | 0 | 6 | ∅ |
| 3 | 0x1 | 9 | 1 | 6 | 0&3 |
| 3 | 0x3 | 18 | 2 | 7 | 3∨4, 0&6 |
| 3 | 0x7 | 6 | 3 | 8 | 3∨4, 6∨5, 0&7 |
| 3 | 0xa | 18 | 3 | 8 | 0&4, 1&3, 6∨7 |
| 3 | 0xb | 36 | 4 | 9 | 3∨4, 0&6, 1&3, 7∨8 |
| 3 | 0xe | 36 | 4 | 9 | 4∨5, 0&6, 1&3, 7∨8 |
| 3 | 0xf | 36 | 5 | 10 | 3∨4, 6∨5, 0&7, 1&3, 8∨9 |
| 3 | 0x1d | 36 | 5 | 10 | 3∨5, 0&6, 3∨4, 1&8, 7∨9 |
| 3 | 0x4e | 9 | 5 | 10 | 4∨5, 0&6, 1∨2, 3&8, 7∨9 |
| 3 | 0x4f | 9 | 6 | 11 | 3∨4, 6∨5, 0&7, 1∨2, 3&9, 8∨10 |
| 3 | 0x54 | 6 | 5 | 10 | 0&5, 1&4, 2&3, 6∨7, 9∨8 |
| 3 | 0x55 | 36 | 6 | 11 | 3∨5, 0&6, 1&4, 2&3, 7∨8, 10∨9 |
| 3 | 0x57 | 36 | 7 | 12 | 3∨4, 6∨5, 0&7, 1&4, 2&3, 8∨9, 11∨10 |
| 3 | 0x5e | 36 | 7 | 12 | 4∨5, 0&6, 3∨4, 1&8, 2&3, 7∨9, 11∨10 |
| 3 | 0xee | 6 | 8 | 13 | 4∨5, 0&6, 3∨5, 1&8, 3∨4, 2&10, 7∨9, 12∨11 |

## Why the lower bounds cover all circuits

A point or line incident to an edge is essential. Turn on one of its neighbors and toggle the vertex while all other vertices are off. In a minimum circuit for a nonempty relation, fix isolated inputs false and propagate constants, including the nullary gates. Bypass unary gates and gates with repeated operands. Remove gates outside the output cone. A missing output reads false and an input alone cannot compute a nonempty edge function. The resulting circuit ends at a binary gate with distinct earlier operands. Every gate and every essential input except the output has a consumer.

With g gates and v essential inputs, the connected circuit graph has at least g+v−1 operand edges and at most 2g, hence g≥v−1. For every remaining candidate size below the witness, the CNF offers both operations and every pair of distinct earlier operands, allowing arbitrary fan-out. Its clauses fix the output on minimal true inputs (the edges) and maximal false inputs (maximal independent vertex sets). This suffices for a monotone function. Among all topological numberings of a circuit, choose the lexicographically least list of operand pairs and operations. Two adjacent independent gates cannot occur in descending order there, since their exchange would decrease the first differing entry. The order clauses enforce that necessary condition. The empty graph instead uses zero gates. The Lean replay checks each generated CNF using `Std.Tactic.BVDecide.LRAT.check`.
