# Read-two replacement for plane-incidence circuits

Research by James Adams (Jamesadams1988) on L-meta-2582.

For a projective plane of order `q` with `N = q² + q + 1` points, the desk asks whether every binary monotone circuit computing incidence has a read-two replacement of at most the same size. **The case below the star construction’s size is open.** A read-two circuit must have, for each minimal true input, a single proof tree that uses each selected variable at most twice. The tree may differ between minimal inputs. [Upstream definition](https://github.com/open-goat/pequalnp-proofs/blob/1972ec9f567e2b3c90b0adc5472172f7e5ddfab0/lean/PEqualNP/Defs/ReadK.lean)

## Where the replacement is proved

The pinned upstream proof of L-meta-2393 constructs a read-one line-star circuit with exactly `N(q+2)−1` gates. The Lean proof here shows that every vector feasible at a smaller read bound occurs at the larger bound as well. Combining these results proves the assigned replacement conclusion for every circuit with at least `N(q+2)−1` gates. A hypothetical counterexample must be smaller and must itself fail read-two. [Threshold proof](threshold/Threshold.lean) · [Read-bound monotonicity](threshold/ReadMonotone.lean) · [Upstream star construction by willakone](https://github.com/open-goat/pequalnp-proofs/pull/4638)

A second argument handles a conjunction of OR clauses whose truth implies incidence. If its accepted pairs occupy `t` rows, all row degrees are between 3 and `m`, and `t ≥ m`, row stars fit within the removable gate budget when its AND gates are private and at most two frontier OR outputs must be retained. With no retained frontier outputs, the saving is at least two gates. The formal statements count distinct wire IDs in an abstract block graph. Applying the saving to a particular circuit requires identifying the block and proving that the gates charged to it can be removed. [Counting and Boolean replacement](factors/README.md) · [Private-gate hypotheses](factors/private-frontier.md)

For a full conjunction of positive raw-literal clauses, the minimum number of clauses equals the number of distinct unions of point neighborhoods. The counts on the coordinate planes of orders 2, 3 and 4 are respectively 37, 704 and 25,237. [General Lean proof](factors/ExactClauses.lean) · [Finite enumeration](clauses/README.md)

## How to check a candidate

Given a circuit known to compute incidence, Lean proves that testing joint read-two on its incident pairs suffices. Each gate can use a table with nine entries, one for each allowed pair of leaf counts. A separate proof shows that keeping only nondominated counts gives exactly 19 distinguishable states for a deterministic gate-by-gate evaluator on one fixed pair. This minimum concerns the evaluator’s states. [Official-definition equivalence](IncidenceRead.lean) · [19-state proof and scope](algebra/README.md)

The packed Python implementation agreed with an independent capped-vector implementation on all 659 point–line pairs of the three planes. One control modifies a single point-star in the 27-gate Fano circuit. The 30-gate result still computes incidence on all 16,384 Boolean inputs. Every incident pair passes the two scalar checks, but the three lines through the modified point fail the simultaneous test. In isolation, four binary gates are necessary and sufficient for a two-input circuit computing AND to separate those checks. [Three-plane replay](packed/README.md) · [Localized Fano control](localized/README.md) · [Two-input census](control/README.md)

## Replay

Run `bash replay.sh /path/to/pequalnp-proofs/lean` from this directory using Python 3.10 or later, Git, Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The checkout must contain commit `1972ec9f567e2b3c90b0adc5472172f7e5ddfab0` in its Git history. The replay checks the source digests of the original star construction and the upstream read-vector helper, builds those modules in a temporary directory, and checks the research proofs against the project definitions. All finite controls are reproducible locally.
