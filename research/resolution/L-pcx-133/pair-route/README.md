# An exact local cost in bit pigeonhole resolution

James Adams. The L-pcx-133 assignment asks for a refutation of the five-pigeon, four-hole formula in at most 127 lines. The hole of pigeon *i* is its pair of bits. Each of the 40 input clauses forbids two named pigeons from occupying a specific hole. The size counts input clauses, semantic weakenings and binary resolutions. The underlying rules and formula are defined upstream. [Resolution rules](https://github.com/open-goat/pequalnp-proofs/blob/68d8de6866df4e70ba92793c839867835e87b145/lean/PEqualNP/Defs/ProofComplexityLin.lean) · [Bit pigeonhole axioms](https://github.com/open-goat/pequalnp-proofs/blob/68d8de6866df4e70ba92793c839867835e87b145/lean/PEqualNP/Defs/ProofComplexityBit.lean)

For a fixed pair of pigeons, deriving the two-equation clause “their first bits differ or their second bits differ” from their four collision axioms takes **exactly 11 lines** in the four-variable subsystem. Preparing all ten pairs separately therefore takes 110 lines. A subsequent proof tree using only these prepared clauses requires at least 18 binary resolutions. This gives **at least 128 lines** for that construction. The tail may reuse pair clauses as leaves and use arbitrary parities of all ten bits and arbitrary semantic weakenings. The tree hypothesis requires each derived tail line to have at most one use. The unrestricted 127-line question permits shared derived lines and different preprocessing.

## Why one pair costs eleven lines

Write *D* for the target clause and fix the first pigeon. For each of the four holes *h*, replace its collision axiom by the equivalent clause “*D* or the first pigeon differs from *h*.” This costs four axioms and four weakenings. Resolve twice on the first bit of this pigeon and once on its second bit to obtain *D*.

The standalone Lean theorem `Row133.OnePair.upper` checks this eleven-line schedule for pigeons 0 and 1 in the full five-pigeon formula. Its reported axioms are `propext`, `Classical.choice` and `Quot.sound`.

For the lower bound, `pair_minimum.py` encodes every ten-line local derivation. All four axioms must occur because removing one admits the assignment placing both pigeons at its hole. They can be placed first, and a shorter proof can be padded with a duplicate weakening. Each later line has 30 Boolean membership variables, one per nonconstant parity equation on the four bits. Other variables specify a previous line for weakening or two previous lines and a parity for resolution. The encoding tests the exact syntactic union after pivot erasure. For weakening, it compares truth values on all four equal-hole assignments. The other twelve assignments satisfy every input and, by soundness, every line.

Two simplifications preserve the budget. The constant false equation can be deleted from every line. Tautological lines can be dropped because a resolvent with a tautological parent is a semantic weakening of the other parent, and weakening a tautology produces another tautology. The supplied independently replayable certificate derives the empty clause from the 994-variable, 9,495-clause encoding using 10,212 reverse unit-propagation steps.

## Why the tail needs at least eighteen resolutions

Consider the 240 assignments with exactly one colliding pair. Each of the ten pairs labels 24 assignments. When a derived clause is false, traverse the proof backwards. A weakening leads to its false parent. A resolution queries its pivot parity and leads to the false parent on that side. At a leaf the unique collision identifies its pair. Discarding unary steps and queries constant on the surviving sample gives a binary parity decision tree for these labels.

At each node, the number of different surviving labels bounds the leaves below it. The script checks every nonzero ten-bit parity at the root. For each resulting child, it minimizes the sum of the two label counts after one further informative query. The minimum over roots is 19 leaves. A binary tree with 19 leaves has 18 internal nodes. The computation uses these two levels only, so 19 is a lower bound on full decision-tree leaf count.

| Two-level lower bound | Number of root parities |
| ---: | ---: |
| 19 | 15 |
| 22 | 30 |
| 25 | 150 |
| 27 | 60 |
| 32 | 768 |

## Replay

Run these commands from this directory with Python 3.10 or later and assertions enabled. They use the standard library.

```sh
python3 -B pair_templates.py
python3 -B check_pair_lrat.py pair10.lrat.gz
python3 -B pair_tree.py
```

The first command checks every semantic weakening on all 1,024 assignments and checks syntactic resolution. It also demonstrates a three-step inference from the three pair clauses of a triple of pigeons. In either chosen bit the three pigeons cannot all agree. One weakening followed by two resolutions proves the claim for that bit. The tree script independently enumerates all 1,023 possible nonzero pivot forms.

To regenerate the SAT instances or the proof, use CaDiCaL 2.1.2. The ten-line instance reports UNSAT (exit 20) and the eleven-line control reports SAT (exit 10).

```sh
python3 -B pair_minimum.py 10 pair10.cnf
cadical --lrat --no-binary pair10.cnf pair10.lrat
python3 -B check_pair_lrat.py pair10.lrat
python3 -B pair_minimum.py 11 pair11.cnf
cadical pair11.cnf
```

To replay the optional Lean witness, set `file` to the absolute path of `OnePair.lean` and run the following from the upstream `lean` project directory at the linked revision. It uses Lean 4.36.0 and the project's built dependencies.

```sh
lake build PEqualNP.Defs
lake env lean -j1 "$file"
```

The full prepared derivation is also available. Lean checks that its first 110 lines contain all ten pair clauses. Three further steps derive a clause saying that the first bits of pigeons 0, 1 and 2 cannot all be equal. To replay it, use the same command with the path to `PairPrefix.lean`. Both declarations use only standard kernel axioms. [Full derivation](PairPrefix.lean)
