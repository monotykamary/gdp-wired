# Lane E — guarded inclusion integration

Branch: `claude/mldr-incl`. **NOT GATE GREEN; AUDIT BLOCKER; no merge claim.**

The audit code repair is committed as **`3f976cba`**, with archive-preflight
ordering corrected in the follow-up. On boat, `mldr-incl-audit-check-v2` passed
type/lint and **31 tests**, including the exact duplicate-protocol regression.
`mldr-incl-audit-source-smoke/results-v2` passed both a real two-revision pair
and a tampered-candidate archive rejected before either proof. The first
tamper smoke failed and is retained; neither it nor the corrected smoke is a
full merge gate. **All v1 pass flags remain withdrawn.**

Lane D rejected the v1 paired-gate analyzer: counts alone did not enforce the
exact roster, pair identity could change between sides, and the candidate SHA
was not bound. All v1 `pass:true` / component-pass claims are **withdrawn**.
Raw logs are retained only as diagnostic observations. The replacement enforces
the independent exact roster and both source archives; acceptance will use
Lane D's one-command final gate.

Production commits: **`f6ec83db`** (ordinary preference), **`7dc52140`**
(raw lazy-pool admission and shared-cap correction). No kernel rule, trusted
fact, protocol-name branch, or proof-budget increase was added.

## Implementation

The generic member matcher reaches `rawBuild` through `grammarPool`. Entries
use existing semantic deduplication, fresh witnesses, the pool cap and proposal
meter. Initial preference shares the ten-slot bound with picks. A scalar
residue is never asserted: each entry is the ordinary count-witness
disjunction, and source branches and final certificates pass the unchanged
kernel. Tests cover immutable inputs, exact-witness reuse, full-cap refusal,
missing flags, a checked generic conditional proof, and rejection of its
unguarded strengthening.

## Verified receipts

* `runs/mldr-incl-check-v8/`: type/lint and all four focused files passed:
  **89 tests, zero failures**. This supersedes the earlier cap-expectation
  failures; their logs remain retained.
* `runs/mldr-incl-shards-v1/`: all seven full-suite shards passed on boat:
  **1,073 tests passed, 18 skipped, zero failures**, with one pinned large VM per
  shard and zero starts charged to the batch.
* `runs/mldr-incl-gates-v1/`: historical diagnostic logs report IC3Syn 84 vs
  83, DuoAI 10 vs 10, and zero broken proofs. **These are not accepted gate
  evidence** because v1 did not bind the exact roster/pair identity/both SHAs.
* `runs/mldr-incl-baseline-v1/`: three unchanged original MLDR trials remained
  UNKNOWN at strict 60 seconds (job times 59.59, 59.61, 59.57 seconds).

These are not the full paired merge gate.

## Conditional safety: the failure is now localized

The first 24-job matrix lost its client during scheduler recovery, but its
completed logs were recovered from the exact owned admission before closing
that admission. No other client's batch or VM was touched. The frozen
baseline safety archive has **39 files, zero omissions**, SHA-256
`b96c779fda332e17778af88d76e69a8682b98de04739c1e07e6d3d4b154c0f0c`.
It is retained as `research/mldr-incl/fixtures/safety-gp1.br`.

At the 2,700-unit share with Gp1 (generated laws plus a supplied p1 hypothesis):

| Configuration | Result | Checked proof | Counted units | Instrumented wall |
|---|---|---|---:|---:|
| Baseline | SAT / not proved | no | 1,868.570 | 1,887.404 ms |
| Lane B completion only | SAT / not proved | no | 1,868.570 | 3,335.020 ms |
| Completion + Lane E pool | SAT / not proved | no | 1,868.570 | 2,623.211 ms |

These are one-law diagnostics, not proofs of the whole family, not original
harness passes, and not a fair uninstrumented wall-time comparison.
Completion is Lane B's `60b8c37a`, applied only in isolated experimental jobs.

**Observed blockers:** before the first numeric query, the shared proposal
meter has already consumed all **65,536** steps. The selected certificate has
only five reads. In the final raw STEP goal, quantified count laws already
supply packed quorum-count reads, but the selected certificate still has five
reads. The trace does **not** expose the full proposal pool: it cannot alone
distinguish failed pool population from failure to refresh the initial
selection. Separate full-pool/selected-certificate diagnostics and controls
test those hypotheses. The stage-0 and stage-26 packets preserve the direct
observations, including phase/work counters.

The current fast loop compares nine distinct frozen STEP packets at
250/1,000/2,700 units, across raw, preferred, own-key completion, and
witness-seeded modes: **108 independent jobs**. A separate eight-way real-E-14
experiment limits optional pre-query refinement and moves completion earlier.
Four additional controls refresh preferences when new count reads arrive,
without increasing the existing proposal ceiling or safety share. Neither
research scheduling variant has been put into production.

## Real E-14 input

`runs/mldr-incl-e14-generation-v2/` completed on boat from Lane A `1681e8e5`:
**35 generated laws, zero proof queries**, generation wall 23,359.980 ms.
No hand law was added. The result includes the count-cube p1/TypeOK forms.
The exact archive is `research/mldr-incl/fixtures/e14-generated.br`, SHA-256
`4b97fb96467ee51e9b80ff0a13b33f00d2731452fd93e6191f65c17c8882d64a`.

## Infrastructure and remaining work

The earlier recovery/quarantine window invalidated incomplete client receipts;
retries and recovered raw receipts are identified separately. The two-job v3
conditional client subsequently hit its outer queue-wait timeout. Its two
completed payloads were later recovered from the exact owned admission: base
and preferred both remain SAT at 1,868.570 counted units (instrumented walls
2,012.967 and 2,505.420 ms). They are diagnostic payloads, not a successful
client/gate receipt. Actual proof limits were not extended.

The documented generic `queue add` accepted the 108-job backlog, but this
repository's custom treadmill only consumes idea-tagged entries. Its exact
owned, still-queued entry was marked withdrawn (receipt retained), and the
same jobs were submitted once through `supercomputer run --class submission`.
No scheduler resource policy, ownership guard or other submission was changed.

Section **16.6** is now the active instruction: use the actual frozen 35-law
family for conditional safety until Lane A 16.1/16.2 lets the original harness
reach safety, then replace this measurement with the real attempt.

Remaining before merge: checked conditional improvement on Gp1 and real E-14;
strict original-harness confirmation; 29x3 paired versus current main, DuoAI,
broken variants, bar, and final type/lint. All failures remain in the evidence.
No MLDR proof improvement, integrated sub-60-second result, merge, or push is
claimed.
