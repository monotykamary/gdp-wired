# a8bbe098 follow-up measurements

Status: independent receipt checks, all ten native p1 replays and the
CPU-qualified regression audit completed. Commitlint and the final
1,646-file tooling source check passed; production is unchanged.
The gated commit and all production paths remain unchanged.

## For lane B

Five alternating-order pairs compare exact `a8bbe098` with validated control
`97463c56`, on one exclusive Ryzen 7 9700X, Bun 1.4.3. Both sources report
**1152.3382236 p1 units in every repeat** (ratio 1.0), with checker-only replay.
The +77.63% fallback-first regression does not reproduce on a8. Its existing
mixed-clause repair has count-source SHA-256
`7a4c830848afa2d05393bdd00c546393092cf1f94d5ce9cdee8a2aad9189abd4`.
No additional scheduling patch or new candidate is justified by these results.

The candidate's three whole-Paxos repetitions prove. The historical 97463c56
cost control is unknown in all three whole-Paxos runs and is not the work
baseline. Against the retained whole-Paxos work baseline, the candidate retains
**6,915,544 solver / 1,037,946 full work**. These are canonical runner results,
separate from the conditional p1 diagnostic.

**Scope:** the cost probe deliberately uses Lane B's exact historical P*
family `5dbdbf...`. It is not an original-model Inv* or 29/29 result. Lane B's
new original 43-law family `f5b807...` does not contain the historical p1 target.

## Named candidate-only loss

The unchanged `core/effect-queue.test.ts` case **the CLI on the pool** passed
**5/5 on baseline 8214a543 and 5/5 on a8bbe098**, alternating which source runs
first. All ten fresh processes ran on one exclusive EPYC 4585PX (eight pinned
vCPUs), Bun 1.4.3. The 900,000-ms test timeout and 30-second CLI proof allowance
were unchanged. There are zero candidate-only losses in this cohort.

The earlier candidate-only unknown remains recorded. Five new passing pairs
mean **not reproduced here**, not proven noise, not a repaired cause, and not
a full-suite or independent Lane D gate pass.

## Evidence and failed audit

Measurement batch `20261110-080834-7ilqre` completed both workers with exit 0.
Placement, original collected logs and summary remain in
`runs/lane-i/gated-follow-up/`.

The first audit (`20261110-092000-c78bnb`) correctly refused the p1 packet:
its original collected log was exactly the collector's 400,000-byte tail,
which omitted source receipts and the first pairs. No evidence requirement
was relaxed. The complete original stdout (**816,127 bytes**) and empty stderr were
recovered through the Boat API from the p1 worker's retained snapshot.
Remote/local stdout SHA-256 matches:
`777245aa64a873fe8800229a597cfce9c2c5d37d545a231b36293de4886f29cb`.
The audit must also verify that the recovered file ends with the exact
previously collected tail. SSH recovery timed out; API recovery succeeded,
and the resumed VM was stopped. No measurement was rerun.

The complete-log audit in `20261110-092542-j9am19` verifies all ten native
p1 replays, complete effect-test outcomes, source hashes and the recovered
tail. Its later source check passed TypeScript but rejected one new-tool
control-regex lint error. The ANSI parser was corrected.

`20261110-093728-40hczh` then passed ten parser self-checks and type/lint on
its 1,645-file snapshot (zero warnings/errors; zero OOM delta), but its
commitlint step could not find a CLI because this repository does not
install that development tool. An isolated installation subsequently hit
commitlint’s Git-root requirement for `--edit`; reading the same files via
stdin passed in `20261110-095211-rt8xfl`. The new regression auditor also
needed an explicit string-sort comparator; its final source check and
fresh receipt audit passed in `20261110-095250-95qs99`, with zero OOM delta. No proof measurement was rerun for these tooling corrections,
and every failed receipt remains.
Recovered audit result: `runs/lane-i/gated-follow-up-audit-v2/result.json`.

## Current Lane D RED entries

The complete CPU-qualified audit found zero candidate-only losses in all
nine cohorts. Protocol: 35 paired repetitions / 70 proven runs across the
EPYC 4585PX, Ryzen 9 9950X and Ryzen 7 9700X. Inference: 5/5 per side.
Sums: five full-file runs / 35 native cases per side. All original budgets
are unchanged; five non-EPYC eligibility skips are excluded from counts.

Under the coordinator's threshold (three candidate-only losses in five
pairs), none is a reproduced regression. Request Lane D adjudication;
do not promote the full gate or claim a discovered flake cause.
Full timings, source/CPU custody and receipts: `lane-d-adjudication.md`.
## Integration queue

`helper-integration.json` records the refreshed readiness boundary. B now has
an original-family capture and original conditional components, but shared-
allowance composition and remaining custody/census/pairs are still pending.
F improves frozen-harness op0 to its original local allowance, but still has
legacy canonical routing and open ops 1/5/6. E's genuine normal attempts
remain unknown. All stay unmerged/off by default; no wholesale lane merge.
