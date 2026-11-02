# Lane COUNTS — gen/counts

Initial base db9e3c2; fast-forwarded to main 6bdeb95 on coordinator request. Implementation is untrusted and opt-in; no default-search/checker changes relative to main.

## Delivered
- core/count-facts.ts exports countsForReads, proposeCountFacts and proposeCountPicks: bounded Venn identities/subsets/quorum instances, read adapter and model-guided concrete picks, all existing certificate language.
- core/COUNT-FACTS.md documents Q3 integration, freshness, caps and the mandatory final checker path. Q3 stayed read-only; no external solver.
- 21 distinct frozen snapshots: 20 auditable, 19 mismatching fixed models rejected, one count-consistent model; one flattened snapshot lacks definitions. After refinement: 18 modeled, three unknown, zero closed.
- Includes nine original cases, six later Paxos cases, four distinct earlier hand cases (decision proposed included), an additional anonymous hand case and residual mldr.
- Stable gzip inputs/models and manifest under kernel/fixtures/count-facts; tests registered beside main's data-synth tests.
- runs/REPORT.md: per-goal/family audit, limits, future Lean statements (not implemented), integration and complete gate ledger.

## Verified
- Post-merge runs/counts-main-6bdeb95: counts 143/143 and shards 1,3,4,5,6,7 pass.
- runs/counts-main-6bdeb95-retry: check and unchanged shard 2 pass on isolated boat VMs; check uses 8 GB Node heap after initial 2 GB OOM. No solver budgets/test timeouts changed.
- Two quick-bar attempts only. Second: runs/bar/runs/counts-quick-2, frozen pre-merge counts vs db9e3c2: wrong 0, no solid losses in completed views, 6/6 Lean replays. All 34 paired timing ranges overlap (runs/speed-bands.json).
- Its g332 candidate row was invalid due to data loading, not a solver loss. Targeted paired recovery in runs/g332-recovery fixes the missing data link and hard-link tar extraction in isolated runner copies only: 332/332 proven each side, all search signatures identical. See summary.json.
- No third, full or post-merge quick bar. Default search unchanged, so no IC3Syn/DuoAI run. No trusted changes, so no new trusted-rule proof/mutant gate.
- All owned jobs finished; automatic Modal fallback occurred only after three boat failures and applications are stopped. No push/GitHub writes. User-owned brief.md preserved.

Q3 next: consume the opt-in module at its candidate hook, retain returned witnesses/picks through pool truncation, and check the final certificate. Model elimination is not protocol closure. Local recovery stash remains recorded in runs/counts-stash-ref.txt; no history was rewritten.
