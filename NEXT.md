# Timing-bound IC3Syn — gen/timing-astra

## Outcome
Implementation complete; protocol/test/quick-bar gates passed. No push or GitHub writes.
Base: main c6036e6, including EPR-clock. Robust had not landed at the final main check.
Full evidence: runs/REPORT.md; earlier iterations: runs/REPORT-history.md.

## Acceptance
- runs/gate5: all four targets3/3 under strict60s, explicit four-vCPU affinity on isolated boat large VMs. Slowest target45.141s.
- IC3Syn24/29 proven in every run vs main23/29, no every-run losses. Learning_switch3/3.
- DuoAI9/10 every-run on both sides: the same first consensus_wo_decide repetition timed out; repetitions2/3 were10/10.
- Check, all7 shards and focused regressions pass. All29 broken variants paired: none proven.
- Stock quick bar: runs/bar/runs/timing-astra-final/REPORT.md. Wrong0, no solid losses in any view. No disjoint slowdown among33 common three-run timing tests; one base-only test failure retained. Lean6/6.
- g332 recovered a hard-link archive extraction issue via the stock fallback after3 boat failures; both final fallback apps stopped with0tasks. See runs/g332-archive-diagnosis.md and runs/final-modal-apps.json.

## Implementation
Shared reader terms and incremental counted queries; direct shared-set induction instead of preliminary cone reproving; per-law counted-pass eligibility reset; bounded tree/sample reuse; witness-first bitmaps; compiled sample-law checks; honor requested cube widths during construction; defer persistent-state copies until requests pass preconditions.
No protocol-specific knobs, budget/rate changes, or trusted-checker changes.

## Handoff
No remaining checks for this task. Full trusted mutants were not run (untrusted search/runtime changes only); stock bar checked its6 Lean certificates. Timings are measured three-run evidence, not a guarantee against arbitrary future VM stalls. Earlier failed gates remain documented, not discarded.
Owned worktree scheduler batches were closed, and all launched checks were awaited. Preserve the run directories and user-owned untracked brief.md.
