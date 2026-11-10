# Original-model generator intake and revised finish line

Active integration is `4d8289ce`, merging new gate baseline `b11e1f65`.
Qualification-only ref: `claude/lane-i-generator-b11e1f65`, commit
`279c45b3bb2e8655c98931958962ff51314cd4bd`. It has the same executable
sources as staged `ee6a78c3`, whose targeted tests, roster check and type/lint
passed on boat in `20261110-100830-si838c`. Main’s historical run-file
deletions are honored; the conflicting local report and admission file
were untracked rather than physically erased. A 26,429-byte delta pack
adds b11’s missing objects to the existing source cache; no tree is copied.

## Staged generator delta

Lane A sources: `ef509fab` (deterministic finite work prefix), `7d76eb71`
(loaded-row proposals), `3f271711` (identity fixture), `e59d8352` (count-first
admission), `b1ee0778` (compiled Boolean marker). No model re-encoding is
included. The sole merge conflict combines the new finite `tick()` with
the existing rejecting-law/revived-state tracking; neither is removed.
Both new core test files are registered. Only eight production/test/roster
paths differ from the active integration source.

`preflight.ts` requires exact protected source blobs, unchanged original
model `0541fa9436e307a6fb716aa5064637b30b893b79`, targeted tests, roster
completeness, type/lint, actual Q2 and guarded Inv1758 ASTs, and identical
candidate bodies/names across three qualified generation runs. Until this
passes, do not claim intake or launch the full proof qualification.
Existing source packs and a small patch are reused: no new local tree copy.

## Quiet qualification

`quiet-host.ts` uses the exact fresh-Bun CPU/memory workload from Fable's
committed `research/track-fable/hostvar.sh`. Bracket each measured run;
require steal at most 0.1% and both pre/post probes within 10% of the frozen
per-model floor (also retain the published 165/650-ms ceilings). Calibration
must have at least three accepted probe samples before publishing a floor.
Noisy attempts are retained and relocated, never averaged into a pass.

First scout batch `20261110-100350-yscr8r`: six workers on three VMs, only
EPYC 4585PX and Ryzen 9950X. Quiet-admission unit checks passed, but remote
calibration `20261110-100724-oykv07` found no eligible model floor. Do not
use these hosts as qualified. Alternate-size scouting is still running.

Additional default-size probes (`20261110-101624-cjgq7v`) and combined
calibration (`20261110-101809-ny7ox9`) establish one eligible floor: Ryzen
9700X, 150 ms CPU / 442 ms memory, four admitted probes. The floor is
frozen before any qualified generation results. Three default-size workers
now attempt three original-model generations each; every attempt still
requires both probes and run-wide steal <= 0.1%, with each probe loop
within 10% of this floor. This is not three-CPU determinism qualification.

The three first workers (`20261110-101941-ss4cjo`) were all rejected
**before generation** on `bx_3x8cqc5e`. Independent boat audit
`20261110-102443-dd6pmj` confirms 1.4–3.1% steal and 9.3–12.2 s memory
probes: zero qualified cohorts and no generator calls in that batch.
The floor is not weakened. The paired census is prepared but not complete.
Its initial pilot stopped in type/lint with exit 134 before any census run;
the exact current tooling subsequently passes on the established large
profile (`20261110-102733-q5nysf`). The decoded abort is an explicit V8
JavaScript heap-limit failure near 2 GiB, not evidence of a kernel OOM kill
(`oomDelta=0`, `kernelPidOom=false`); it says nothing about the historical
unattributed SIGKILL. The abort receipt remains retained.
Section 18 has now landed and been read in full; isolated I1–I3 work may
proceed alongside Lane A, with no weights or W selected by this lane.

Source preflight `20261110-100830-si838c` passed targeted tests, roster
and type/lint on the executable-equivalent staged source. A separate
new-baseline tooling check (`20261110-101555-9qos8n`) passes after
correcting two unused destructured bindings in this research runner. The
failed first check is retained; no production repair or test rerun was needed.
The planned commit message also passes remote commitlint. Structural diagnostic
`20261110-101300-tocfye` reports a 49-law original family with Q2 at index
39 and guarded Inv1758 at index 41 (canonical hash
`bf8f3627f2e60969dcf6861c4e83be5f0920e2972c324a57f947f1752a77e3a5`).
It is explicitly unqualified: not a proof, census, or timing acceptance.
All protected source blobs remained unchanged. All receipt processing runs on boat; zero subagents.

## Revised finish line: sequence and acceptance

Read `MLDR-29.md` → `FINISH LINE, REVISED` (2026-11-10). The historical
60-second ×3 gate remains the fallback until all prerequisites land.
After a8 adjudication and generator intake:

1. Lane A removes every internal wall-driven stopping decision.
2. Lane I implements Fable Section 18's **single complete-work counter**:
   certificate checking, table construction, instance construction,
   sampling, finite filtering and all other expensive paths. Kernel edits
   are instrumentation only; no proof is accepted/rejected differently
   when the counter is observed without a budget. Lane D audits this.
3. Lane I runs all 29 original protocols repeatedly on at least three CPU
   models, comparing exact verdicts and counts and reporting first phase
   divergence. Do not label elapsed-time equality as determinism.
4. Lane D fixes one qualified reference host and calibrates W once to 60 s.
   Final target: 29/29 under W, then one quiet wall-clock confirmation.

Section 18 was not yet present in the design document at inspection. Do
not invent weights, call the partial old work meter complete, set W from a
noisy run, or count current wall-limited results toward the new finish.

Throughout intake preserve the current schedule's cost constraints:
p1 1152.3382236 units and canonical Paxos 6,915,544 solver / 1,037,946 full
work under the historical meter. Keep those legacy-meter comparisons
separate from the later complete-meter calibration and three-CPU census.
No helper or saved P* family is enabled by this staging.
