# BAPA p2: symbolic consensus ports

The eight consensus entries in `models.ts` now use symbolic `size` (Node) and
`values` (Value), no upper bound on either. Empty sorts admit no request that
names one of their members. Unary maps retain their one-coordinate keys;
binary relations use native tuples, never a fixed-radix integer key.

The scope is the **same canonical majority interpretation** as the prior ports,
not arbitrary quorum families or the separate original-Ivy naive-consensus
experiment. `members` counts Q below the symbolic Node size, and `majority`
requires Q to be a subset and strictly more than half the nodes. The stored
VotingQuorum and initial setup in consensus_forall/wo_decide are unchanged.

Safety and bugs are unchanged: singleton chosen/decided values or a unique
leader; broken voting permits repeated votes. No helper invariants are supplied.
Function-valued Vote maps still use value + 1 with zero for Nil, as before.
Consensus EPR's nondeterministic request-message add/delete writes the original
(i,j) tuple and reads its original (j,i) tuple guard.

Small checks keep the exact existing TLC constants, choices, projections and
`uses` reductions, replacing only tuple decoding and adding symbolic parameter
values (3 nodes and 2 values, or 3 values for consensus). The three stored-quorum
choices in consensus_forall/wo_decide remain the configuration's three two-sets.
The naive-consensus decide projection remains TLC's existing DecideView.

`research/bapa/consensus-sized.test.ts` exercises all eight at size 66 in
the interpreter (also the compiled runtime for uncounted consensus), checks
original broken traces, zero-domain/endpoint rejection and the
absence of the old cap/radix in machine and safety ASTs. These tests are not an
all-size proof. Only a checked exported theorem quantified over the size params
may establish that claim; results and receipts are reported separately.
