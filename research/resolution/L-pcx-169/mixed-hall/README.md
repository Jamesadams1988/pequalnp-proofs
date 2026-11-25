# A 157-line minimum for mixed Hall expansions of unary PHP(5,4)

The ordinary resolution construction that expands one new pigeon at each level has 157 lines. Allowing each Hall clause to expand on its own choice of either a pigeon or a hole still requires 157 lines, even if the proof reuses identical intermediate clauses. This bound concerns the two specific constructions below. Other resolution proofs, including ones that resolve these intermediate clauses in different ways, remain open to shorter derivations.

## Two allowed constructions

Let the pigeons form a set P of size 5 and the holes form a set H of size 4. Write A × B in a clause for all positive literals x(i,j) with i in A and j in B. For S ⊆ P and T ⊆ H of sizes k+1 and k, write U = H ∖ T. The clause at this node is S × U. At k = 0 it is a pigeon axiom. The root at k = 4 is the empty clause.

For any r in S and h in T, the child (S ∖ {r}, T ∖ {h}) has clause (S ∖ {r}) × (U ∪ {h}). Resolve away its k positive literals in column h using the respective collision axioms involving r. This derives the conditional clause consisting of ¬x(r,h) and (S ∖ {r}) × U. The k collisions can be applied in any order.

* **Pigeon expansion.** Choose r in S. Build a conditional for each h in T. Starting at the pigeon axiom for r, resolve successively with all k conditionals on x(r,h), in any order.
* **Hole expansion.** Choose h in T and an anchor a in S. Start with the child missing a and h. For every r in S ∖ {a}, build the conditional at r,h and resolve it into this starting clause on x(r,h), in any order. This uses all k+1 children missing h.

Either expansion uses k² conditional resolutions and k final resolutions. The signed clauses within one expansion have different negative literals or different numbers of surviving positive literals. In the final sequence each further step removes a previously surviving pivot. Thus each of its k(k+1) results is distinct.

## Counting required Hall clauses

Fix one expansion for each used node. If a node has several available derivations, retaining just one for the counting argument suffices. Pick a uniformly random bijection from P to H together with one extra symbol. Starting at the root, reveal matched pairs as follows.

* If a pigeon r is selected, reveal its image. Stop if it is the extra symbol. Otherwise follow the child missing r and its matched hole.
* If a hole h is selected, reveal its preimage r and follow the child missing them both. The anchor child is among the possible children.

Given the complete revealed history on a surviving path, the remaining bijection is uniform. At level k, the pigeon step survives with probability k/(k+1), and the hole step always survives. The probability of reaching level k is therefore at least (k+1)/5. Reaching any specified (S,T) requires the bijection to map S onto T together with the extra symbol. That event has probability 1/binom(5,k+1). Consequently the number of distinct required level-k nodes is at least

    (k+1)/5 × binom(5,k+1) = binom(4,k).

For levels 1 through 4, this gives respectively 4, 6, 4 and 1 nodes.

## Counting actual resolution lines

An intermediate clause cannot pay for expansions at two different nodes. The accompanying exhaustive check takes every (S,T) in this instance, generates every single resolution transition in either construction over all choices and operand orders, and compares its literal set with all other nodes' results and with the axioms. The subset of pivots already eliminated determines the current clause, so enumerating all subsets and each next pivot covers every order. The numbers of different possible internal clauses at levels 1 through 4 are 120, 1500, 2540 and 451, with unique node ownership. This includes the output of each expansion. A parent may freely reuse that output as a premise.

Each pigeon axiom is necessary because a bijection of the other four pigeons into the four holes violates only the omitted pigeon axiom. Each collision axiom is necessary because placing that pair in its hole and the three remaining pigeons bijectively in the other holes violates only that axiom. The 45 axioms and the distinct resolutions give at least

    45 + 4×2 + 6×6 + 4×12 + 1×20 = 157 lines.

Choosing pigeon expansions with one fixed pigeon order uses precisely binom(4,k) nodes at level k and attains the bound.

## General form

The same argument applies to n+1 pigeons and n holes. For every nonroot node, U is nonempty. A signed intermediate identifies its pivot pigeon r and hole h from its only negative literal. Deleting every literal from column h leaves precisely (S ∖ {r}) × U. This recovers S and T. At the root the deletion leaves no literals, which also identifies that node.

For a positive nonroot intermediate the pigeon support is S. The holes occurring positively in every one of these pigeon rows are exactly U. All other surviving positives are confined to one pivot row, or to one pivot hole in a proper subset of those rows. Thus a positive intermediate also identifies its nonroot node uniquely. Root intermediates are distinguishable. They are empty, have just one pigeon, or occupy a single hole on at most n−1 pigeons. Nonroot intermediates have at least two pigeons. If all their positives occupy one hole, then U has size one, so their pigeon support has size n.

The survival bound is (k+1)/(n+1), and the matching probability for a given node is 1/binom(n+1,k+1). Exactly binom(n,k) nodes per level suffice with a fixed pigeon order. For n ≥ 2 the minimum number of resolution lines in this family is therefore

    Σ [binom(n,k) × k(k+1)] = n(n+3) × 2^(n−2).

Adding n+1 pigeon axioms and n × binom(n+1,2) necessary collision axioms gives the total proof length. For n = 4 the expression recovers 157.

## Replay

Run `python3 check.py` with standard Python 3 from this directory. The check verifies each possible resolution transition, literal-set ownership, all 120 bijections for each node and its pivot choices, and the final counts.
