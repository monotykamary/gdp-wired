# Independent VERIFY-ALL audit

Baseline: `6a3874d3f2c6febe40bb14775884cb327a2cce3c`. No engine, kernel, model or original harness source is edited. Final report: `runs/VERIFY-ALL.md`.

All substantive work runs on boat (`supercomputer --skill`). From this worktree:

```sh
supercomputer run --jobs research/verify-all/jobs-production.json --out runs/verify-all/production --class submission --timing --vm-type large --backend boat
# Produce baseline archive with git (not a worktree), then paired DuoAI controls:
mkdir -p runs/verify-all/base-data
git archive --format=tar 6a3874d3f2c6febe40bb14775884cb327a2cce3c > runs/verify-all/base-data/base.tar
supercomputer run --jobs research/verify-all/jobs-duo-paired.json --out runs/verify-all/duo-paired --class submission --timing --vm-type large --backend boat --data runs/verify-all/base-data:verify-base-data
supercomputer run --jobs research/verify-all/jobs-capture-all.json --out runs/verify-all/capture-all --class submission --timing --vm-type large --backend boat
supercomputer run --jobs research/verify-all/jobs-replay.json --out runs/verify-all/replay --class submission --timing --vm-type large --backend boat
```

- `run-production.sh` runs the original harness with strict external 60-second KILL, 60,000 ms search budget, and four explicitly pinned vCPUs on an exclusive large VM. Installation and source hashing precede the timer. 87 IC3Syn searches, 30 DuoAI searches, 29 broken cases. Both wall and counted work (where the original harness emits it) remain in logs; no result is synthesized for killed jobs.
- `run-duo-pair.sh` alternates archived-baseline/current ordering on one exclusive pinned VM, three times for each of ten protocols. Only the search runs: hand-written `human` families are skipped.
- `capture.ts` is supplementary instrumentation, not the primary measurement. Bun loader wrappers observe actual return objects of `proveRule`, `proveLaws` and `proveSetFast`; the existing `countsDump` output-only hook records a closed family after checking. They do not supply a law, change a result or replace search. Capture adds overhead and its results are reported separately from the uninstrumented run. The unchanged original harness still prints its own verdict.
- `export-captured.ts` rechecks saved proof objects and exports their retained trees/counted certificates. Ordinary trees seed the emitter’s effective plain machine; sum side-goal trees must already be in the packet. Counted families use `cmachineToLean`, with a checked original-machine projection preserving every original count definition. Existential and sum extensions get explicit original-law bridges; their projections may differ only in bound-variable names. No proof search or replacement family is used. It also replays captured refutations, reviving carried maps and checking preconditions, legal steps and actual stated safety predicates (not the fixed small-instance `p.bad` diagnostic).
- `check-lean.sh` compiles unchanged Lean sources and checks the generated theorem with `decide +kernel`, never `native_decide`, `sorry` or an external solver. Logs include the theorem's axiom dependencies. Finite time/resource limits and export failures are not proofs.
- `recheck-archives.ts` reads compressed certificate packets embedded in completed logs and replays/re-exports them, without repeating production search. Large packets beyond the output cap are explicitly marked unavailable.
- `analyze.ts` parses completed log files and hashes them. A zero shell exit is never interpreted as proof: each internal harness/export/Lean status is inspected.
- `tlc-*`, `model-source-*`, `engine-trust-*` implement independent audit tracks. See their reports for source identity, precise commands, limitations and failure evidence.

Final assembly uses `jobs-report-base.json` → `report-base-final/`, `jobs-capture-metadata.json` → `capture-metadata-final/`, then `jobs-build-report.json` with `--data runs/verify-all:evidence`. The builder verifies emitted Lean hashes against their actual check receipts; its `REPORT_BEGIN`/`REPORT_END` payload becomes `runs/VERIFY-ALL.md`. `jobs-check.json` runs repository TypeScript and type-aware lint checks; `paxos-diagnostic.*` isolates the failed independent check.

`jobs-finalize.json` runs the final full check, builds the report with all links/hashes checked by `verify-report.ts`, and runs commitlint against the file-backed message using the existing Conventional Commit rules. Its final receipts are under `runs/verify-all/finalize-confirm/`.

Raw logs, placement records, source manifests and large certificates belong under ignored `runs/verify-all/`, not git. Preserve first failures and retries. Do not clean caches, change external solver settings or tune the engine in response to findings.
