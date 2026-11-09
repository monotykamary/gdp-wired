# Lane E — guarded inclusion integration

Branch: `claude/mldr-incl`. **NOT GATE GREEN; no merge claim.**

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
* `runs/mldr-incl-gates-v1/duoai/`: **10/10 proofs on both sides**, zero lost
  proofs, against current main `b788e195`; the other gate components are pending.
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

**Falsifier found:** before the first numeric query, the shared proposal meter
has already consumed all **65,536** steps. The initial certificate pool contains
only five reads. In the final raw STEP goal, quantified count laws already
supply the needed packed quorum-count reads, but the certificate pool still
has only those five reads. Adding a late completion callback cannot repair a
pool whose shared proposal meter is already exhausted. The stage-0 and stage-26
packets preserve this directly, including phase/work counters.

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
