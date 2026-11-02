# Lane Q (gen/laneQ): where it stands, what is next

Branch gen/laneQ = gen/laneC3 + gen/laneY6 (the mldr probe) + main 3000a12. Untrusted changes only (no Lean needed):
core/counts.ts (lazy count instances and picks, CEGAR), kernel/cdcl.ts (the counted search's models: a leaf's integral
LP point, branch and bound at a fractional one), kernel/prove.ts (brokenOf reads left-out cells at given values).
Research knobs: GDP_COUNTS_LAZY (wide default | 1 | 0), GDP_COUNTS_POOL (1000), GDP_CDCL_POINT=0, GDP_COUNTS_GIVEN=1
(callers alone), GDP_COUNTS_PROF / GDP_COUNTS_TRACE=23 (per attempt: wall, counted, phases, MBQI rounds, lazy picks).

Gates on 64af398/07ef2f3 (DESIGN.md, gen/laneQ section): IC3Syn 70 vs 69 runs within 60 s, 23 vs 21 protocols every
run, no broken variant proven; DuoAI ten 30/30 vs 29/30; quick bar wrong 0, lost 0 solid; shards 10/10.

paxos_epr and mldr are NOT closed. What blocks them:
- paxos_epr: the search does not propose the propose phase's invariants (Qs joined at pr, the checked rows below
  pmaxr, pmaxr's proposal). Even the hand set (research/protocols/quorum/paxos-hand.ts, GDP_COUNTS_GIVEN=1) leaves four
  step goals unknown at 40 s counted each: one value decided, decision has votes, choosable, busy rows (busy rows reads
  no count: the check phase's rowOk instance at a composed key j = a·N + b is likely never asked by modelInstances).
- mldr (mldrprobe.ts): the five quorum/term laws' Houdini step goals (ls 30-34) stay unknown at 31 s counted each
  (CEGAR picks 58-93 of the ~1000 pool instances; 790-2400 hyps over the MBQI rounds; grow>300 dominates). IC3Syn's
  mldr lacks the Endive invariant altogether.

Next, in order:
1. modelInstances: bind a quantified flag's single key against a composed read (Vote[cnt·N² + j] vs Vote[c·N² + a·N + b]
   gives j = a·N + b); then re-run paxos-hand GIVEN=1 for busy rows.
2. Dump the four paxos-hand unknowns' goals (GDP_COUNTS_DUMP) and check them with Z3 offline (research only) to tell
   "true but hard for grow" from "needs more instances".
3. Count-relevance for the CEGAR pool: relate two counts only where their bodies read a common map (cuts mldr's 84-93).
4. The counted clock under-counts the elimination's equality substitutions (core/solver.ts solve's first loop, no
   work.n): a 5 s-counted decide ran 176 s wall on paxos-hand before this lane's fix.
Fast loop (coordinator): paxos_epr and mldr one run each + sentinels consensus_epr, consensus_forall, firewall,
client_server_ae, twophase; full gates only when one closes.
