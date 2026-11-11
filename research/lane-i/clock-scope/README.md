# Counted-scope clock integration — verified patch

Source target: lane A `5aa7681815e41a939fed137783b656abeeacc1e6`.
Read D's `research/verify-all/f4-f5-cd671ac1/RESULT.md` in the verifyP worktree.

The active integration branch predates A's scopes and has a different trusted
checker (`e557bc6c…`, versus A's `5a5973de…`). Do NOT copy A's kernel into it.
This patch is developed and checked on an exact disposable archive of A.
It modifies only the clock helpers before `grow()` in `kernel/prove.ts`,
`core/wall.ts`, and `core/trace-clock.ts`. The entire trusted kernel/Lean tree
except the clock-containing prover is hash-checked against A; the prover's
`grow()` and all following implementation bytes are compared unchanged.
No checker or certificate semantics are changed or promoted.

A already routes `core/counts.ts`'s `ptime` through traceNow and uses counted
admission tiers, borrowed unreserved work and bounded dispatched generation.
The remaining telemetry hole was a captured/bound performance.now. The patch
suppresses wall telemetry in full-work mode and nested legacy counted scopes:
zero means unavailable telemetry, not elapsed milliseconds or work units.
Inherited counted scopes also use the counted clock in searchDateNow,
searchNow, cancellation and transport helpers. A's counted withWall deadlines
are retained (scoped endpoints come from clock/searchWall, never epoch time).
Wall fallback exists only outside counted scopes.

The tripwire is preloaded before source modules, catching previously captured
clock functions as well as ordinary Date.now/performance.now lookups. Tests
exercise generation, sampling/ptime, checked true/false admission, nested
scopes, finite deadlines, exception unwinding and unscoped full-work mode.
The unpatched A baseline must fail on nonzero captured wall telemetry.

## Current runs

Initial `20261111-023011-tsckvj`: the unpatched A baseline correctly fails on
nonzero captured wall telemetry. The two patched jobs stop at an explicit
manifest existence check (nonexistent core/work-budget.test.ts); this is not
a test pass. Retry `20261111-023045-0hmxa6` exposed a serialized newline error
in the generated trace-clock module; receipts are retained. This was fixed,
not hidden by a relaxed test. Legacy-only child-process tests are now run only
with GDP_WORK_FULL=0, since they intentionally assert the disabled profile.

`20261111-023122-3q6z3e`: all 26 full-work tests / 563 assertions passed. The
legacy run exposed an unscoped step-profile telemetry path (36 pass / 1 fail),
now guarded too. Full typecheck could not resolve vendor imports because git
archive omits submodule contents; prepare.sh now includes exact pinned vendor
archives. Both failed overall receipts remain preserved.

Final `20261111-023225-a7qmv5` passed 37 legacy tests / 622 assertions,
26 full-work tests / 563 assertions, and type/lint on 1,730 files. Its full job
exit 1 was only commitlint needing a Git root in the disposable archive. That
runner prerequisite is corrected; isolated commitlint retry
`20261111-023343-69iuf9` passed. All owned batches are terminal.

Apply-ready source commit: **353713c9** on **claude/lane-i-counted-clock**,
parent **5aa76818**. It changes only the three clock modules and adds the two
tripwire files. All 131 other kernel/Lean files and the complete prover tail
from grow() onward match A byte-for-byte. `core/counts.ts` is unchanged: the
ptime fix is transitive through its existing traceNow call, exercised by the
sampling/generation control. No kernel checking or certificate rules changed.
The clean temporary source worktree was removed. The integration branch's
older trusted checker remains untouched; this is not a bulk A or B/F merge.

Inputs are prepared in `/tmp/lane-i-clock-input`, including exact source.tar
and trusted-tree.txt from `git archive` / `git ls-tree` at the source pin.
Runner is the existing tiny `/tmp/lane-i-raw-census-41d39043/runner`:

```
supercomputer run --jobs research/lane-i/clock-scope/verify.jobs.json \
  --out runs/lane-i/clock-scope --class gate \
  --data /tmp/lane-i-clock-input:clock-input
```

Refresh changed assets into that input directory before a new, uniquely named
output run. Heavy checks only on supercomputer; leave `.reflex-saved/` alone.
B/F common-kernel promotion still requires D's GATE receipt.
