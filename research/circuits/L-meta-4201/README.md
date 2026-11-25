# OR gates for the incidence function of PG(2,4)

Research by **James Adams**. L-meta-4201 asks whether every fan-in-two monotone circuit for this function needs at least **104 OR gates**, with no bound on AND gates or wire reuse. The input selects among 21 points and 21 lines. The output is true precisely when a selected point lies on a selected line. With both classes numbered modulo 21, point `p` lies on line `l` when `l − p` is one of `0, 5, 7, 17, 20`. [Exact target](https://data.pequalnp.com/data/lemma/L-meta-4201.a624ce9c44c2.json) · [Pinned upstream sources](https://github.com/open-goat/pequalnp-proofs/tree/27b35fd75abe0e1ab60ea57b18c40c49115242d2) · [Project discussion of edge functions](https://pequalnp.com/papers/note-1)

| Result for arbitrary circuits | Evidence |
|---|---|
| At least 40 OR gates | `Row4201.fortyOR` uses the three standard Lean axioms. Starting with an edge, a path through all 42 vertices forces a distinct OR for each of the next 40 vertices. [Proof](PGForty.lean) |
| At least 41 OR gates | An induced six-cycle needs five ORs, and the other 36 vertices force 36 further ORs. `Row4201.fortyOneOfNoFour` proves the transfer with the finite four-OR exclusion as its hypothesis. `Row4201.fortyOneNative` discharges it with `bv_decide` and has an additional native-evaluation axiom. A separate SAT encoding and LRAT certificate corroborate the finite exclusion. [Transfer](PGFortyOne.lean) · [Native proof](PGFortyOneNative.lean) · [SAT certificate](certificate/) |
| At most 104 OR gates | `Row4201.Upper125.upperWitness` proves a 125-gate circuit correct on every input with the standard axioms. Each point takes four ORs to combine its five incident lines and one AND to test that point. Twenty more ORs combine the 21 point terms, for **104 ORs and 21 ANDs**. [Witness](Upper125.lean) |

For a restricted class the construction is optimal. The circuit first forms unions of singleton input supports, then takes products of two supports. Every product must contain only genuine incidence edges. Since two distinct points share only one line, every nonempty such rectangle is a star. The proof charges at least 104 ORs across the input unions and the unions forming the output, even with free deletions from previously formed output supports. An arbitrary circuit can create a product containing nonedges and remove them later. The open question is whether those intermediate products, or more general alternations of AND and OR, permit a circuit with at most 103 ORs. [Rectangle theorem](RectangleTruth.lean) · [Free-deletion extension](FilteredOutput.lean)

The upper bound instantiates the project's existing cover-circuit construction. Earlier upstream reductions include KainanP's finite search over OR rows and piotrduperas's biclique-cover normalization. The results here give an explicit restriction to a six-cycle and a bound for sound rectangles with later deletions. [Cover-circuit construction](https://github.com/open-goat/pequalnp-proofs/blob/27b35fd75abe0e1ab60ea57b18c40c49115242d2/lean/PEqualNP/MetaComplexity/Helpers/CoverCircuitList.lean) · [Finite-search reduction](https://github.com/open-goat/pequalnp-proofs/pull/8801) · [Biclique-cover reduction](https://github.com/open-goat/pequalnp-proofs/pull/11026)

## Testing a candidate

Exactly **25,342 input/output tests** suffice for any monotone circuit. The 105 minimal true inputs select the endpoints of a single edge. The 25,237 maximal false inputs select a set of points and all their common non-neighbor lines, with the points in turn equal to all common non-neighbors of those lines. Lean proves the test criterion and the count of 105 edges. Exhaustive enumeration gives the count of maximal false inputs. [General criterion](ExtremalVerifier.lean) · [Plane verifier](PlaneVerifier.lean) · [Candidate checker and controls](candidate/README.md)

This suite has minimum cardinality among fixed input/output tests for unrestricted monotone functions. If one minimal true input is omitted, flipping only its output to false preserves monotonicity. Flipping only a maximal false input to true does likewise. Each omitted query therefore leaves a different monotone function consistent with all the other observations. This argument also covers fan-in-two monotone circuits of unrestricted size, since each such function can be expressed as a disjunction of its minimal true conjunctions.

## Replay

Use the pinned upstream checkout with its Lean toolchain and Mathlib cache. From this directory, run the Lean modules and candidate controls with the first command. The second command replays the independent LRAT certificate with the Python standard library. The third tests a JSON circuit against all 25,342 inputs.

```sh
./replay.sh /path/to/pequalnp-proofs/lean
python3 certificate/verify.py
python3 candidate/verify_candidate.py circuit.json
```

The replay prints the Lean axiom dependencies so the native finite result is visible alongside the standard-axiom proofs. The Python certificate verifier checks 10,070 reverse unit propagation additions, then evaluates a five-OR six-cycle witness on all 64 assignments. [Certificate files](certificate/)
