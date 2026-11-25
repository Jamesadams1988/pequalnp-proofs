# Verifying a PG(2,4) circuit

Run the reference star circuit, a candidate JSON file, or the regression controls with Python 3. The verifier uses only the standard library.

```sh
python3 verify_candidate.py
python3 verify_candidate.py candidate.json
python3 test_verify_candidate.py
```

An input circuit supplies a list of gates and a natural-number output index. Each gate has the form `["or", [i, j]]` or `["and", [i, j]]` with zero, one or two operands. The 42 inputs precede gate outputs. A missing wire reads false at the time of evaluation. Empty AND evaluates true and empty OR evaluates false. An invalid gate or negative index is rejected. The exit status of a valid candidate check is zero if its Boolean function is correct. The output reports its OR count and whether that count is at most 103 separately. The assigned conjecture requires at least 104 OR gates for every monotone circuit computing the function. [Official statement](https://data.pequalnp.com/data/lemma/L-meta-4201.a624ce9c44c2.json) · [Circuit definitions](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/CircuitLowerBounds.lean)

## The 25,342 test inputs

Point wires have indices 0–20 and line wires have indices 21–41. In the incidence test below, a line index ℓ ranges from 0 to 20. A point p and line ℓ are incident precisely when (ℓ−p) mod 21 belongs to {0,5,7,17,20}. The target is true when the selected points and lines contain an incident pair. Its 105 minimal true inputs are the incident pairs.

To enumerate maximal false inputs, fix a set P of points and select the set L of all lines incident with no member of P. Keep (P,L) exactly when P also contains every point incident with no line of L. These complementary-neighborhood tests give 25,237 distinct maximal false inputs after considering all 2²¹ choices of P.

For a candidate function g computed from AND and OR gates, accepting all edge inputs proves that the target's true set is contained in g's true set. Every true assignment contains an edge. Rejecting all maximal false inputs proves the converse inclusion. Every false assignment is contained in a maximal false one. The verifier evaluates all tests together with integer bitsets.

These test inputs are necessary for any fixed test suite that certifies equality by querying an arbitrary monotone Boolean function. At a single minimal true input, change the target value to false. Every proper subset already had value false, so the modified function remains monotone. At a single maximal false input, changing its value to true likewise preserves monotonicity. Each modification agrees with the target everywhere except the one omitted query. Such monotone functions have fan-in-two AND/OR implementations, for example by disjoining their minimal true conjunctions. This necessity result assumes no size bound on the candidate and uses only input/output tests.

## Controls and scope

The reference circuit computes one five-line disjunction per point, gates it by that point, then disjoins the 21 terms. It uses 104 ORs and 21 ANDs. Replacing either input choice of each OR by a unary copy of the other operand produces 208 candidates with 103 ORs, each of which loses an incident pair. Adding point 0 with nonincident line 1 gives a false positive on a maximal false input. The controls also check constants, unary gates, duplicate operands, future reads, absent outputs, and rejected JSON index or gate types.

The tests establish full Boolean equality for each candidate they check. The 208 bypasses establish irredundancy under these specific edits to the reference circuit. Deciding the unrestricted lower bound would require addressing all other monotone circuits with at most 103 OR gates. For background on the distinction between a single-output circuit and a system of line disjunctions, see the project's literature discussion. [Edge-function note, §7](https://pequalnp.com/papers/note-1)
