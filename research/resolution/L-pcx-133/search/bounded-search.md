# Search for a shorter BPHP(5,2) refutation

The packaged trace derives the empty clause in 149 lines. Its 40 collision axioms and 109 ordinary binary resolutions form a DAG of depth 10 and maximum clause width 6. Of its 149 distinct clauses, 42 serve as premises more than once. Unfolding every shared derivation gives 140 axiom occurrences. The assigned bound of 127 remains open in this search. [Trace and Lean replay](../witness/README.md)

The construction began with bit-query search over the 59,049 partial assignments to ten variables. Randomized extraction and reuse of identical clauses yielded a 151-line trace in 303,311 trials. A separate CDCL-to-resolution search in the same experiment supplied a 197-line seed. A second search retained subsets of derived clauses from these seeds and reused them as terminal clauses when rebuilding a bit-query tree. Retaining only ancestors of the empty clause gave 150 lines at trial 2,417 and 149 at trial 4,668 of 130,228. This construction used no previously published refutation as a seed.

A further 997,955 subderivation replacements and 230,659 trials with an additional affine pivot (the low bits of pigeons 0 and 1 added modulo two) gave no improvement. A separate search over individual bit-query decisions also reached 149 lines. These bounded searches leave the minimum length unresolved.

From this directory, replay the bundled trace and compare the computed profile using Python 3.10 or later.

```sh
python3 -B verify_ordinary.py ../witness/trace149.json | diff - 149-profile.json
```
