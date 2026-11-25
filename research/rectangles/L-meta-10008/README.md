# Covering the nonincidences of the 31-point projective plane

James Adams · November 25, 2026

The assigned matrix records which of 31 points lie on which of 31 lines. It has 775 zero cells. A zero rectangle selects points and lines with no incidence between them. L-meta-10008 asks whether **at least 18 rectangles** are necessary to cover all the zeros. Upstream has proved at least 15 and exhibited a cover with 21. We have not closed that interval. [Assigned statement](https://pequalnp.com/desk/step?gap=L-meta-10008) · [Upstream lower bound](https://github.com/open-goat/pequalnp-proofs/pull/17199) · [21-rectangle construction](https://github.com/open-goat/pequalnp-proofs/pull/15942)

**Any 17-rectangle cover needs at least nine rows and nine columns that each belong to three or more rectangles.** If all rows have at most two memberships, the minimum is exactly 24. A pencil of six lines gives a matching construction. The proof counts how many points can be distinguished on one line using two-coordinate labels. The package checks the construction on the literal matrix for every rectangle budget up to 24. [Proof, construction and scope](degree/README.md)

**The fractional minimum is 155/12.** A compact certificate covers every zero cell exactly 48 times using 620 rectangle occurrences. Every zero rectangle has area at most 60. Together the two counts give matching upper and lower bounds when fractional weights are allowed. [Certificate and replay](fractional/README.md)

**Local changes to the published cover face a specific obstruction.** Removing any seven rectangles from the 21-rectangle witness and inserting six cannot produce a complete cover. Every hypothetical 17-cover therefore shares at most ten of the original rectangles. Our 20-rectangle candidate still misses cells. The checker lists them explicitly. [Local-exchange proof](exchanges/README.md) · [Search and partial certificate](search/README.md)

The pinned upstream revision is `41fe834b000fc5190f11224bb9e6bc645249cc7b`, using Lean 4.36.0 and Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The public fork contains local research certificates. The original 17-rectangle question requires a separate official checker decision on its exact statement.

Further checks identify the exact fooling-set size of six, give lower bounds for covers with specified symmetries, and classify precisely when three maximal 6-by-10 rectangles can cover one row. These restrictions can be used to prune candidates before a full cover search. [Fooling sets and source audit](review/README.md) · [Group-restricted covers](symmetry/README.md) · [Row-shape constraints](constraints/README.md)
