# Paxos counted-certificate diagnostic (baseline 6a3874d3)

## Conclusion

**Item 4 remains failed for Paxos.** The retained accepted TypeScript family has **two independent Lean rejections**, not one. This investigation neither changes the production model/checkers nor replaces, repairs, or searches for a proof. No conclusion that Paxos safety itself is false follows from this failure.

| Zero-based law index | Captured law | Exact rejected check |
|---|---|---|
| 12 | `scan-prefix:cnt:rowOk:d93992f463f488aa` | `cEntryOk` → `key2Ok` → `skFresh s 29 = false` for further key `k$21` |
| 20 | `carry:co-write:6282256ba10ee781` | step `checkMC` → `checkCountedW` → `checkGoalLemmas` → main `checkTLemmas`/`checkT = false` |

All seven top-level machine checks printed true, all five count declaration checks printed true, all 25 entries' witness checks printed true, and all 50 start/step certificate checks except law 20 step printed true. Every entry condition except law 12 printed true. TypeScript `checkCountedLaws` and all 50 individual `checkMC` calls printed true on the exact retained packet.

### Law 12: identified side-condition mismatch

The emitted further key `29` is `k$21`, also the bound key of quantified flag `72`. `key2Ok` in `lean-kernel/Sets.lean:933` requires each further key to satisfy `skFresh`; `skFresh` at line 926 refuses a name occurring in any quantified-flag body. The diagnostic prints the actual flag body and finds this occurrence. All other `key2Ok` conjuncts are true (including key/primary-key inequality, exclusion from external variables, precondition and initial state, and compatibility with the other laws).

This is not failure of this law's start or step refutation: **both checkMC results are true**. It is a machine/law freshness admission condition absent from the TypeScript `checkCountedLaws` wrapper (`kernel/kernel.ts:2090`), whose body checks obligations via `witsOk` and `checkMC`. The existing exporter interns identical textual names into identical Lean variable indices (`lean-kernel/emit.ts:367–424`), so it preserves this collision. Determining whether a sound bound-variable renaming bridge could discharge this restriction is outside this diagnosis; no renaming or replacement certificate was attempted.

### Law 20: narrower unresolved checker/export boundary

For `carry:co-write:6282256ba10ee781 @step`, Lean accepts:

- all named hypotheses as members of its generated goal (`namedIn = true`, missing hypotheses `[]`);
- declaration key restrictions, read freshness and read/witness separation;
- conversion of reads to counts;
- counted witness freshness and count-instance resolution;
- certificate table well-formedness (`wfTab = true`).

There are **no lemma cuts** in this certificate. The remaining failure is the main encoded tree (`checkTLemmas ... [] tree = false`, hence ordinary `checkT`). This is distinct from law 12's admission failure.

The final diagnostic additionally encodes the exact TypeScript `mcGoal` for this step, using the original emitted name map, with the existing `encode` function and **the same retained tree**, not a new proof. It compares those literal hypotheses with Lean's reconstructed full counted hypotheses and checks the direct goal/tree. The terminal kernel output is `("bridge20", true, false)` and `("differing_hyps20", [])`: the full hypothesis lists are identical, and even direct encoding of that TypeScript goal with the retained tree is rejected. This excludes differing reconstructed hypotheses as the immediate cause of this obligation failure; the remaining boundary is tree encoding versus checker semantics. It does not establish which leaf/row operation is ultimately responsible. An emitter defect versus TypeScript/Lean arithmetic/tree-checker disagreement remains unresolved. Do not describe this as a proven soundness exploit or as an independently verified Paxos certificate.

## Evidence and reproduction

Read inputs: user `VERIFY-ALL.md`, `COMMON.md`, `supercomputer --skill`; existing `capture.ts`, `export-captured.ts`, `check-lean.sh`, `recheck-archives.ts`. All substantive extraction, TypeScript checks and Lean computations ran on boat. Laptop activity was reads, git/status, edits and supercomputer scheduling only.

Input: `runs/verify-all/capture-all/capture-paxos_epr.log`, `ARCHIVE_BEGIN` base64 xz tar. Exact original retained objects:

- packet SHA-256 `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386`
- generated Lean SHA-256 `e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1`

`research/verify-all/paxos-diagnostic.ts` asserts both hashes before checking anything. It copies only definitions before `theorem verified_check` into a separate `/tmp/paxos-diagnostic.lean`, adds `#reduce` diagnostics, and uses kernel reduction, not `#eval` or `native_decide`. The rejected original theorem and its consequent error-induced `sorryAx` are not imported into the diagnostic. Diagnostic elaboration failures listed below were rejected, never accepted as evidence of a theorem. No replacement safety theorem is generated.

Commands (same job file each time, progressively refined diagnostic script):

```sh
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-deep --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-deep2 --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-detail --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-final --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-terminal --class interactive --data runs/verify-all/capture-all:evidence
```

Job command:

```sh
bun install --frozen-lockfile >/dev/null && bun research/verify-all/paxos-diagnostic.ts && bash research/verify-all/check-lean.sh /tmp/paxos-diagnostic.lean
```

Job allocation: `cpu:4`, `memory:14336`, `timeout:1800`, `vm_type:large`. These are diagnostics, not production timing claims. The scheduler's shell exit code is not the job's verdict; use each output directory's `summary.tsv` and job log.

| Output directory suffix (under runs/verify-all/) | Boat batch | Job exit | Job seconds | Outcome |
|---|---|---:|---:|---|
| paxos-diagnostic | 20261109-090337-5yqi57 | 0 | 55.73 | identifies two failures |
| paxos-diagnostic-deep | 20261109-090503-rou41h | 1 | 47.9 | diagnostic-only `Inhabited CEntry` indexing error; not trusted |
| paxos-diagnostic-deep2 | 20261109-090819-bnnp1u | 0 | 55.57 | isolates key2Ok and counted-tree checks |
| paxos-diagnostic-detail | 20261109-091017-b2pjj5 | 0 | 50.74 | isolates skFresh; count witness/table checks true, no lemma cuts, tree false |
| paxos-diagnostic-final | 20261109-091254-egelwj | 1 | 82.46 | diagnostic-only missing `BEq (List VDef)`; not trusted as final receipt |
| paxos-diagnostic-terminal | 20261109-091634-0i8y7p | 0 | 74.74 | clean comparison: identical hypotheses, direct retained tree rejected |

Each output directory contains `paxos-diagnostic.log`, `summary.tsv`, and scheduler metadata. Lean is 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The clean detail diagnostic SHA-256 is `8935f6e79fd3eb61f65a930637ad567798e69259dfa578723544fe41a70915e5`.

### Final verified hashes and receipt

- Diagnostic TypeScript: `9634e991534fbc5c34b9dd53ebd734fbc91f9f3ffe2c1d4055960b5608f7cbe5`
- Job file: `725156dc86b0c222c989c72f3f5fd23fd0c219384faeb9de0f7572329cf66d82`
- Final generated diagnostic Lean: `afb426d11a5c457b514bf403501fca355c1b1c08d166a61afc8b33638c6eda7f`
- Final terminal log: `101cb41a6b9e191c98e245186db55a89f6a7cb2c2254d864fec1a4adf799dff3`
- `runs/verify-all/paxos-diagnostic-terminal/summary.tsv`: `paxos-diagnostic 0 74.74 boat`.
- Lean terminal: `LEAN_WALL seconds=68.00 maxrss_kb=3384456 exit=0`.

The final clean run contains no elaboration error or error-induced placeholder. Earlier failed diagnostic attempts remain disclosed above but are unnecessary to the conclusion. All six own scheduler tasks are terminal. Workspace verification: `git diff --stat` empty (tracked baseline unmodified); new files remain under allowed diagnostic names. No commit was made.

## Scope

No production rerun, external solver, core/kernel/lean-kernel/protocol source edits, branch changes, commit/push, cleanup or cache clearing. Boat compilation via existing `check-lean.sh` only. No other worktree writes. All own processes terminate via bounded jobs; no processes were killed. Main owns overall verification totals and final report.
