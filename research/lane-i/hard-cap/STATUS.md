# Active: hard cap plus counter correction on the integration tree

Branch claude/mldr-integ; hard-cap runtime efd70276. Acceptance in RESULT.md:
max 15,000,430 <= 15M+1024; 10 checked proofs/18 unknowns unchanged. 22 tests /
100 assertions; type/lint clean 1776 files; 134 protected identities exact.
All owned batches terminal. No main merge/push; .reflex-saved/ untouched.

D calibration HELD. efd70276 is NOT its pin. User added counter correction:
count tiny constraint nodes, reweight reachability, E1/E2 units vs wall, integrate
and validate cap/no-loss/flags-off, then send ONE exact source pin to D for
174 calibration cases and 29 confirmations. ic3-lean/t1d and ic3-gen/t1f told.
No counter source edits yet. A owns scopes; avoid overwriting its work.

Proposed schema to D: append tinyNodes, reachStates, reachEdges, reachEvals,
reachCompiledEvals; exclusive eval buckets, no subtraction/refund, monotone
root/exclusive conservation. Await schema feedback. D wants raw executed
nodes/branches, pre-step admission, positive weights and no nested resets.
Warned D tinyNodes may be insufficient: pruned 961k/1128s vs341k/3.6s. May need
tinyTerms for generated predicate/interval operations. Proposed reach prior
.02, tinyNodes1 provisional ONLY; not calibrated W.

Fable runnable tree claude/fable-tiny f9923ed0 (A5aa76818 + probes), worktree
../gdp-wired-fable-tiny. Copies in claude/mldr-design cdf1c1e1, worktree
../gdp-wired-mldr-lean (NOT ../gdp-wired-mldr-design). engine-tiny.ts is at
research/track-fable/ in runnable tree; copies in research/track-fable/engine/.
Original script read from pinned git blob, saved /tmp/lane-i-engine-tiny.ts;
README/jobs in /tmp/lane-i-engine-{readme.md,jobs.json}. Fixture family.json,
research/protocols/ic3syn/fixtures/strategy-rejections, hash49a805953627... .
MLDR-DESIGN.md section23.7 read in full. Tests run ONLY via supercomputer.

Representative Fable jobs:
- tiny 0,1 900000 2:341353 nodes/3.6s, drops14,40,42,44,47.
- tiny 0,1 1380000 2 pruned:961473 nodes/1128s, same drops.
- tiny 0,1,73,74 1380000 2:86.2M nodes/346s,+drops4,7.
- tiny 0,1 900000:size3 round0 94.3M nodes/264s.
- reach 1 2:3286 states/75118 steps,250.5Mevals/12.6s;
  same compiled:305.5Mevals/38s. Historical timings unqualified.
- genflow.ts 60000000:552.8Mevals/15.8s yardstick.

Source sites: finite-tiny.ts stats.nodes increments674,693,706. Compiler200-350
emits native predicates/intervals/transitions with no execution counter.
finite-houdini.ts finiteEvaluator + finiteTinyHoudini140. Fable reach custom
BFS in engine-tiny.ts, not core/reachable.ts. New scope needs wrap its evals
and production finiteHoudini paths, entry helpers for states/edges. Source
changes tentatively core/finite*.ts, machine.ts,meter.ts,work-meter.ts,
work-profile.ts; A notified. Current raw-work-v0 exactly8 extras(default1),
plus12 legacy. Schema extension must explicitly reject old weight vectors;
never silently substitute. Preserve trusted checking/Lean byte identities.
