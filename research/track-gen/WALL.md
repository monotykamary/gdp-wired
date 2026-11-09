# T-13 strict-deadline follow-up

Baseline: `189eefcd` (the completed generation implementation, before the wall fix).
Results, failed attempts and final timing table: `runs/REPORT.md`.

## Deadline contract

- `proveRule` with an explicit search budget now encloses preparation, preflight,
  generation and proof in one absolute wall scope. Nested scopes cannot extend it.
- `searchCounted` no longer samples outside its wall or grants `2 * ms` wall time.
- Sampling BFS/walks, sample-law bindings, preflight bindings, counted phases,
  Houdini rounds and refinement loops cooperate with wall expiry. An interrupted
  sample graph is never cached as complete, and an interruption is never a proof.
- The existing counted clock, rate, counters and per-law shares are unchanged.
- Work stops with `min(1000 ms, requested_ms / 20)` of bounded completion headroom.
  This wall-only reserve covers a synchronous operation already in flight and
  result/output overhead; for `--ms 60000` it is 1 s. It applies to all protocols,
  does not inflate counted work, and does not change the external 60 s wrapper.
- Tight binding loops poll on entry and every 256 visited tuple prefixes. Each
  new law/state starts with a fresh poll. Sampling checks each request.

No kernel/solver file, law, trusted fact, original harness or proof budget changed.
The strict process wrapper is the final timing gate, not an inferred timing claim.

## Reproduce on boat

Read `supercomputer --skill`. Use git only to prepare the four changed-existing
source files from the parent; other baseline source is identical:

```sh
mkdir -p /tmp/t13-wall-parent/core
for file in counts.ts exists.ts dsl.ts watch.ts; do
  git show "189eefcd:core/$file" > "/tmp/t13-wall-parent/core/$file"
done
supercomputer run --jobs research/track-gen/t13-wall-final-jobs.json \
  --out runs/t13-wall-final-v2 --class submission --timing --vm-type large \
  --data /tmp/t13-wall-parent:baseline
supercomputer run --jobs research/track-gen/t13-wall-check-jobs.json \
  --out runs/t13-wall-checks-v2 --class gate --timing --vm-type large
```

The first batch contains three sequential baseline/candidate proof pairs, with
order reversed in the middle pair. **Each individual process** runs the unchanged
original harness under `timeout -s KILL 60 ... --ms 60000 --only mldr --skip broken`.
Exit 137 is recorded as a kill, not `unknown` or success. Candidate exit 0 and its
returned JSON are required. `/usr/bin/time` measures startup and output as well.

The same batch compares all 29 generation lists against the parent, split into
three disjoint protocol subsets to avoid serializing the two expensive existing
learning-switch samplers. No subset changes a per-protocol generation budget.
The checks run separately **without** the baseline data mount: those four files
are fragments, not another compilable project under the TypeScript source root.

Decode and validate completed receipts locally (no model/proof execution):

```sh
bun research/track-gen/t13-wall-report.ts runs/t13-wall-final-v2 \
  runs/t13-wall-summary-v2.json
```

The summary includes real exit codes, process and engine wall times, counted work,
complete-attempt prefix comparisons, and all 29 canonical SHA-256 hashes. Complete
canonical lists remain in the compressed receipt logs, outside git. Placement
labels are in each run's `placement.json`; a `large` label alone is not a fixed CPU.
