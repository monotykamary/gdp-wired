# Lane E — guarded inclusion integration

Branch: `claude/mldr-incl`. **NOT GATE GREEN; full gate pending; no merge claim.**

The audit code repair is committed as **`3f976cba`**, with archive-preflight
ordering corrected in **`8d275256`**. On boat, `mldr-incl-audit-check-v2` passed
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
(raw lazy-pool admission and shared-cap correction), and **`0ee27c7a`**
(member upper-bound selection). No kernel rule, trusted
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

The repaired exact-source diagnostic for **`0ee27c7a` vs `b788e195`** has
completed IC3Syn: **84/87 candidate vs 83/87 base**, no lost proofs, no false
proofs, and no lost refutations. All 87 protocol/repeat pairs and both archive
bindings validated. The one gained case is `consensus_forall-r1`; no causal
speedup is claimed. DuoAI is now also validated: **10/10 on both sides**,
with no lost proofs or source/identity errors. Broken variants also validate:
**0/29 proven on both sides**, with no lost refutations. All **126 paired
cases** pass the repaired diagnostic audit, including both source bindings.
This is a complete local diagnostic, **not Lane D final-gate acceptance**; only
that final gate can authorize merge.

These are not the full paired merge gate.

The new-selector seven-shard processes also all exited zero in
`runs/mldr-incl-upper-shards-v1`. Its service log truncates the first shard-7
summary (164 tests), so the visible aggregate is only 909 pass / 18 skip.
A complete-stream, concise-receipt rerun of shard 7 is pending; no complete
new-suite count is claimed from the truncated log.

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

The first frozen matrices are complete and independently checked for receipt,
input-hash and mode/budget identity: **108 Gp1 jobs plus 36 actual E-14 jobs**.
No job produced a checked proof. Each cell below is SAT / UNKNOWN; all proof
counts are zero.

| Input | Raw | Preferred selection | Own-key completion | Completion + flags |
|---|---:|---:|---:|---:|
| Gp1, 27 jobs/mode | 9 / 18 | 9 / 18 | 2 / 25 | 0 / 27 |
| Actual E-14, 9 jobs/mode | 4 / 5 | 5 / 4 | 0 / 9 | 0 / 9 |

Receipts: `runs/mldr-incl-step-v1/analysis.json` and
`runs/mldr-incl-e14-step-v1/analysis.json`. Preferred rebuilds a small
selection rather than preserving all raw instances, so the additional E-14
SAT result is disclosed, not hidden. These are conditional packet experiments,
not original-harness verdicts or a completed proof improvement.

The supported-path scheduling controls proved ineffective: the actual E-14
capture has an empty production support set. Completed ordinary/reserve
controls both returned UNKNOWN at 2,700.734 units; the remaining redundant
controls were stopped and their exact admissions closed. Their partial
receipts are retained under `runs/mldr-incl-recovered/`.

The upper-bound selector in **`0ee27c7a`** passed type/lint and **35 tests**
on boat (`mldr-incl-upper-bound-check-v1`). Scalar guards remain provenance,
not asserted facts. Both new replay matrices completed with exact identity and
input-hash validation: their SAT/UNKNOWN counts are **unchanged from the table
above**, and again no checked proof was produced.

The new diagnostics verify selection of the intended **S-to-full-quorum**
instance, not merely its presence in the pool:

| Input | Preferred | Keyed | Keyed + flags |
|---|---:|---:|---:|
| Gp1 | 24/27 packets | 27/27 | 27/27 |
| Actual E-14 | 6/9 packets | 9/9 | 9/9 |

Evidence: `mldr-incl-gp1-upper-v1/analysis.json` and
`mldr-incl-e14-upper-v1/analysis.json`. Thus the voter inclusion is now selected,
but selection alone did **not** remove the proof-cost or instance gap. The
first six standalone pointwise controls all returned **SAT**, including
stronger and tighter guards: **no checked pointwise proof**. Their reduced
contexts omit original scalar/key-domain premises, so this is not a
falsification of the complete safety implication. A new control adds only
scalar conjuncts extracted from the original raw goal, with a missing-guard
negative, now produces a **checked conditional proof in 39.78 counted units**
using the tighter `CT[i] < CfgT[b]` guard. The original stronger guard also
checks (39.79 units). Omitting the guard remains SAT (35.64 units), ruling out
a vacuous contradiction in the context. Saving and independently rechecking
the conditional certificate is pending. This is **not a safety proof**.

The isolated original-harness A/A+E v1 probe failed all three jobs **in patch
setup**, before any protocol verdict. Lane A changed an import
(`attemptShare`), invalidating the patch context. V2 changes only that context,
passes an exact archive patch check, and is submitted. The pinned Lane A source
is `48533517bf7b6ef1bee47e58d2a9a517babd5488`. These composite probes are not
a full merge gate. V2 completed all three pairs: **UNKNOWN on both sides in
every pair**, at approximately 59 seconds per side. A separate instrumented
A+E capture has 34 initial-family laws and 144 retained / 405 omitted files;
all retained ordinary-attempt stages are pass 0, with no prioritized safety
stage observed. The original-harness improvement is therefore still absent.
The capture hash is
`5926107dd7548316d2c531c7822bb440bf44e17cef3d59bf5340042f92655069`.

## Real E-14 input

`runs/mldr-incl-e14-generation-v2/` completed on boat from Lane A `1681e8e5`:
**35 generated laws, zero proof queries**, generation wall 23,359.980 ms.
No hand law was added. The result includes the count-cube p1/TypeOK forms.
The exact generation archive is `research/mldr-incl/fixtures/e14-generated.br`,
SHA-256 `4b97fb96467ee51e9b80ff0a13b33f00d2731452fd93e6191f65c17c8882d64a`.
The subsequent conditional safety archive is `fixtures/e14-safety.br`, SHA-256
`b9c7abfae8b30ed2c9de6a665aeebc2956599b8ec28fa3d5a97707719e8f3134`: **31 retained
files and 22 omitted files**. Three complete retained early/middle/late packets
were sampled; omitted packets were not reconstructed.

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
