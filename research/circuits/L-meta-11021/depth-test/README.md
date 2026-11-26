# Why four gate levels cannot compute this edge function

The target is true on 455 of 512 inputs. Twelve assignments consisting of the endpoints of a single edge are its minimal true inputs. Thirteen of the 57 edge-free assignments are maximal under inclusion. The finite check below rules out depth four even with free complementary input literals and both constants.

| Condition imposed on a depth-four formula | Greatest possible coverage |
|---|---|
| Its root is OR and it rejects all 57 false inputs. | It can accept 9 of the 12 edge inputs. |
| Its root is AND and it accepts all 455 true inputs. | It can reject 7 of the 13 maximal false inputs. |

Both bounds are attained with positive literals alone. The witness file gives one formula of each kind. A Python verifier evaluates both formulas on all 512 assignments and checks the root, depth and counts. [Explicit formulas](witnesses.json) · [Verifier and optional witness search](witnesses.py)

## Full truth-table computation

Represent a Boolean function of nine variables by eight 64-bit words. Start with constants and the nine variables, optionally including their complements. Close the set twice under binary AND and OR, retaining shallower tables. This gives every function of depth at most two. With signed inputs there are 48,092 distinct tables.

Every function of depth at most three is the AND or OR of two of those tables, allowing a repeated operand. For each such function that rejects every false input, collect the mask of minimal true inputs it accepts. For each that accepts every true input, collect the mask of maximal false inputs it rejects. Keep the inclusion-maximal masks in each family. In an OR at the next level both children must reject every false input, and the root accepts the union of their edge masks. In an AND at the next level both children must accept every true input, and the root rejects the union of their maximal-negative masks. The largest unions give the table above. The 479 maximal edge masks and 29 maximal negative masks are individually identical with and without complementary literals. [Enumerator](full.cpp) · [Recorded counts](full-expected.txt) · [Independent Python implementation](independent.py)

Any ordinary circuit of output depth at most four unfolds into a depth-at-most-four formula by duplicating shared wires. Constants and out-of-range reads are allowed. Unary identities can be removed. Push each NOT through AND and OR by De Morgan's laws, producing signed input literals and a formula of no greater depth. A single terminal may be repeated under a gate when needed. Thus the two root cases rule out all ordinary circuits of depth at most four. The 16-gate circuit attains depth five. [Lean circuit](../upper/Upper.lean)

## A smaller test and its limit

An alternative enumeration restricts the truth tables to the twelve minimal true and thirteen maximal false inputs. Agreement on those tests implies agreement on all inputs for a monotone formula. The enumerator finds nine positive and seven negative samples, each necessary in that particular set, that already rule out depth four for monotone formulas. An ordinary depth-four formula with paid NOT gates can pass all 25 boundary tests. The full-input check above identifies the cost of requiring correctness away from the boundary.

To test a partial specification in the smaller enumeration, an OR node partitions the positive obligations between its children and gives both children every negative obligation. An AND node partitions the negative obligations and gives both children every positive obligation. For a paid NOT, swap the required truth values and decrement the depth budget. The program enumerates these partitions down to depth-two truth tables. [Boundary tests](samples.cpp) · [Recorded inclusion-minimal subset](expected.txt)
