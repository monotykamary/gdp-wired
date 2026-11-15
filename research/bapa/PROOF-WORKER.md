# Single-call BAPA search / closure export (shared)

`research/bapa/proof-worker.ts` is a native **one protocol / one public
`proveRule` call** worker. Use it inside a bounded supercomputer job, not on the
controller. Protocols remain registered in `research/protocols/ic3syn/models.ts`.
Only `p.laws(r)` (the safety property) is supplied: no `p.human`, helper file,
last-proof cache, replacement solver, or second search. A port must not hide
hand-written helpers in its safety-law callback.

```sh
# The outer packet supplies its actual source reference; an uploaded archive
# has no Git root. For an uncommitted gate these are base references only.
export BAPA_SOURCE_COMMIT=<40-hex-commit>
export BAPA_SOURCE_TREE=<40-hex-tree>
bun install --frozen-lockfile
bun research/bapa/proof-worker.ts --only consensus
```

The default output is `$SUPERCOMPUTER_OUTPUT_DIR/<id>`. `--out` must name a new
directory. `--only` accepts one exact ID, never a list or fanout. Use outer
`SUPERCOMPUTER_CONTROLLER=1 SUPERCOMPUTER_NO_BUILD=1 supercomputer run ...
--backend boat`; no Modal imports, nested dispatcher or child VM is used.

## Profile and capture

Before importing core, kernel or model modules, the worker clears inherited
`GDP_*`, `JSC_*`, `BUN_JSC_*` knobs and installs the exact 22 flags in
`profile-049.json`, copied from the original 0.49 generous packet. Only cleared
**names**, not values or unrelated environment, are reported. It requires Bun
1.4.3 and the original executable SHA-256. Default search work is 24 billion
units, or 288 billion for `mldr`. `--work` is a positive safe-integer **diagnostic
work override**, explicitly labeled as such; no inner millisecond limit is
silently substituted. The job must also have a finite outer timeout.

Output-only `core/proof-output.ts` hooks retain the actual returned proof
producer, including inferred/witness/skolem context. Hooks are off by default,
add no public verdict keys, and do not change checker or search decisions.
Capture uses only the scoped public-result observer (never `countsDump`),
snapshots term IDs after all work endpoints exit, then writes lossless data with alias/descriptor/Map/Set and
term-memo metadata preserved. Incomplete files do not get `CAPTURE.json`.

`result.json` distinguishes native `proven`/`checked` from `retention.complete`.
A successful worker exit requires all three, exactly one public call, and an
exact same-machine structural public-law projection. Complete data with an
unqualified projection is kept as `captured-unqualified` and exits nonzero;
this prevents another search when a later checked bridge becomes available.
Missing, stale, ambiguous or cyclic provenance, absent certificates and
unsupported graph data are explicit capture failures,
never permission to search again. A different usual producer machine, missing
public law (including a changed counted law), witness bridge or ambiguous
assembly stays unqualified. Raw counted public-law indices are null when the
original laws are not present unchanged. The reader
recomputes this tag rather than trusting the writer's assertion. Closure/term data are diagnostic native artifacts,
not trusted proof evidence until an appropriate Lean exporter/check succeeds.

Artifacts: `identity.json`, `source-files.json`, `work.json`, `verdict.json`,
`result.json`, and `closure/{CAPTURE.json,graph/...}`. The identity binds actual
runtime, driver, source-file manifest, protocol, profile and budget hashes.
Post-return output errors preserve the native verdict, with a separate output
error and nonzero exit. If even `result.json` cannot be written, stdout retains
the same verdict and reports the receipt-write error. Git commit/tree refs are
**launcher supplied**, not independently verified in
the archive. The included gate refs name its pre-edit base; its content manifest
binds the candidate files actually executed.

## Broken-model option

`--broken` selects the registry's exact `p.bug` variant through `p.make(p.bug)`;
it does not alter the 22 flags, budget, safety-law callback or number of public
calls. The variant is bound in the input hash and result. Its default output is
`<id>-broken`. A proven+checked broken result is labeled
`unexpected-broken-proof` and exits nonzero, never as an accepted capture.

```sh
bun research/bapa/proof-worker.ts --only consensus --broken
```

A negative worker exit alone is not evidence: inspect `variant`, `publicCalls`,
`verdict.json`, and errors. Timeout, startup/capture failure or unknown is not a
refutation. Existing TLC broken traces remain the independent reachable-bug
control. Pinned Bun 1.4.3 batch `20261115-191014-b51mmn` passed: typecheck,
26 tests / 195 assertions, one same-profile broken consensus public call,
`proven=false`, `checked=false`, `stuck=sat`, a native witness and reachable
run, and commitlint. Native job exit 0 in 10.46 s. Recipe:
`research/bapa/proof-negative.jobs.json`. The earlier packet
`20261115-190658-5x8oxz` had malformed launcher metadata and failed before
any public proof call; its failed result is retained, not counted as a negative.
The local six-test run was only a quick contract check, not proof evidence.

## Explicit limits

This slice exports the proof **closure capsule**, not Lean. It never labels a
legacy bounded model as all-size: `allSizesProven` and `leanExecuted` remain
false. A later no-search emitter must consume the captured family, preserve
symbolic sort sizes, and check the original source projection separately.
Resolved some-key, recursive-function, mixed or ambiguous producer routes can
require further exporter support; they must not trigger fallback search.

The capsule code is adapted from reviewed final29 capture commit `0f5ca9d51`;
actual-result observer wiring is from `49b8b591c`. BAPA uses a separate versioned
schema and identity, not a claim to reproduce a historical final29 invocation.
The actual legacy consensus run returns proven+checked and a complete capsule,
but its producer machine differs from the original public machine, so it
correctly exits 2 (`captured-unqualified`). The focused gate expects that
conservative result, not a source-level proof. Only a later checked source bridge
can qualify a genuinely transformed machine.

Focused controls, a real one-protocol capture/tiny-work negative smoke, a
fresh-process capsule read and observation-on/off work-counter parity are in
`proof-worker.jobs.json`. No canonical-29 regression is scheduled by this slice.

## Focused evidence

Batch `20261115-170357-6t6qmn`, native exit 0, 19.02 s of job time:
TypeScript, 24 tests / 183 assertions, fresh-process capsule read, actual
consensus capture with exactly one public call, exact observation-on/off native
counter-vector equality, and a one-unit negative control with neither proven
nor checked. Commitlint passed. Positive native verdict is proven+checked;
source projection remains unqualified and Lean/all-size claims remain false.
Local artifacts: `runs/bapa-proof-worker-03/proof-worker-gate.files/`.

Earlier attempts retained: one zero-launch image-name validation error;
`20261115-165457-xcnnze` stopped at a TypeScript fixture type error;
`20261115-170008-9a0suk` passed 21 unit tests and retained the real consensus
proof, then correctly returned exit 2 for its unqualified source projection.
The final gate explicitly tests that distinction; no source check was weakened.
See `PROOF-WORKER-REVIEW.md` for independent review and fixes.
