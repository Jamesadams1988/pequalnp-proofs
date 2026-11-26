# Fixed schedules with uniform neighbor witnesses

The checker finds a maximum of six flexible pivots in a relaxation of the fixed schedule used in the 30-gate proof. A flexible pivot may be set to either bit. Every live vertex in the certificate has an unpinned neighbor outside the neighborhoods of all previous flexible pivots.

The flexible vertices are independent because the branch that sets both endpoints of an edge to true is constant. In each shore, a new pivot must have a neighbor not covered by earlier flexible pivots from that shore. After all pins, at least one vertex survives. Its witness is a surviving clean vertex, whose own witness is another surviving clean vertex. Their edge has both endpoints outside all flexible neighborhoods.

For each of the 52 possible terminal edges, the enumeration first excludes its neighbors as possible pivots. A subset of one shore admits the freshness ordering precisely when one candidate has a neighbor not covered by the other candidates and the remaining subset admits the ordering. Enumerating independent pairs of admissible shore subsets yields a maximum total of six. This search allows additional schedules by dropping all intermediate live-set tests. It does not evaluate adaptive choices or alternate terminal lower bounds.

Run `python3 cap.py`. The 30-gate Lean proof remains unchanged.
