# T-17: pooled per-law time, original generated-law harness

**Research only. No production/kernel change, complete-law proof, or gate pass. Neither configuration closes the production goal. Inv2973 and Inv* were not generated, so their closure is not tested by this experiment.**

## Experiment and controls

- Frozen production input: `5974b916`, the same `source.tar.gz` used by the earlier research stages, SHA-256 `533e038944924352eb34d1bb03c50a864652aea38e9c6c421a8f21152e2d457c`.
- The original `research/protocols/ic3syn/run.ts` entry point and its generator, compiled once for each of three disposable configurations. No published-family injection, `provePublished`, hand-selected op, or other protocol.
- Command for each prepared bundle: `timeout -s KILL 60 bun CONFIG.js --ms 60000 --only mldr --skip broken`. `--skip broken` omits the separate broken-model comparison, not production generation or proof work.
- Twelve fresh processes: three interleaved baseline/candidate pairs for **each** of pool-only and pool+T-12. Baseline results are not reused between the two comparisons. The same prepared image and machine are reused; no per-run installation or compilation.
- One exclusive large VM, `bx_25xas5gt`, AMD Ryzen 9 9950X, eight of eight vCPUs pinned, no co-tenants. Measurement job: 695.71 s. Audit was separate and ran no proof search.
- Baseline has observation hooks only. Pool changes the law allocator; combo additionally changes the three T-12 policies. All kernel files remain byte-identical. Existing local query/recovery ceilings and row draws remain; the law-level fixed share/4.8-second wall is replaced only in the two research configurations.

## Precisely implemented rule

At the beginning of the harness's timed `proveRule` call, record wall `t0` and normalized counted work `u0`. The shared protocol bounds are `t0 + 60000` and `u0 + 60000`; the external process timeout remains 60 seconds, including startup, and can stop the run earlier. Generation happens inside this timed call and consumes the same remaining wall budget. Its work is never refunded.

For a law dispatch in context `C`, form the actual uninstantiated counted obligations using `countedObligations(m, C, {[law.name]: {}}, index)`. Its weight is the number of expression nodes in **all initial/step hypotheses**, including their contradictory conclusion, summed over the obligations, at least one. Values/names/array containers are not expression nodes. This is a syntactic size, not a relevance or difficulty estimate. Weights are cached only for that context within that process.

`P` is the unresolved ordered suffix in a join round (excluding kept/carried laws), or all not-yet-known laws in the current demand context. Let `w` be this law's weight and `W` the sum over distinct laws in `P`.

```
R = max(0, min(caller counted time remaining,
               protocol counted budget remaining,
               protocol wall time remaining))
A = min(R / 3, R * w / W)
```

A dispatch gets counted and wall deadlines of `now + A`. Its first and second passes share those deadlines; there is no second-pass refill. Subsequent dispatches after context changes use the same decreasing global pool, not a new protocol allowance. Unspent time is available to later dispatches. There is no minimum allowance or last-law bonus: even a lone remaining law receives at most a third.

Combo enables the existing T-12 syntactic-class ordering and model-first natural cases. Its action fallback uses the **same formula** with the current law's `w/W` and the remaining caller/lease counted and protocol budget. The enclosing law wall still applies. This replaces 600, not the remaining production local ceilings. The emitted fallback draws ranged from **0 to 1,134.098 units**, so 600 is not a disguised fixed ceiling.

These are cooperative solver deadlines, not hard real-time per-law interrupts. Observed dispatch-to-next-dispatch spans exceeded a draw by up to **35.459 units / 35.757 ms**, including atomic solver work and intervening bookkeeping; all such work remains charged to the global pool. The external 60-second process guard is unchanged.

The audit checks every emitted draw against the formula and checks pending-law membership. It does **not** independently reconstruct goal weights from journals; that computation is covered by the source/size tests, not presented as a separate proved policy invariant.

## Paired whole-run results

Wall is complete child-process wall, not a sum of solver timers. Units are normalized `fullWork/fullRate`. `>=` is the last observed counted-work prefix of a hard-killed process, not a complete total. A timeout is not a completed unknown result.

| Comparison | Repeat | Baseline units | Baseline wall s / result | Candidate units | Candidate wall s / result |
|---|---:|---:|---|---:|---|
| Pool | 1 | 48,280.614 | 42.364 / unknown | 52,551.767 | 49.729 / unknown |
| Pool | 2 | >=36,941.115 | 60.002 / censored | 41,081.476 | 55.384 / unknown |
| Pool | 3 | 48,280.614 | 58.671 / unknown | 51,554.013 | 51.002 / unknown |
| Pool + T-12 | 1 | 48,280.614 | 59.986 / unknown | 47,136.297 | 52.227 / unknown |
| Pool + T-12 | 2 | 48,280.614 | 57.076 / unknown | 43,981.433 | 53.547 / unknown |
| Pool + T-12 | 3 | >=43,247.646 | 60.001 / censored | 39,424.656 | 55.487 / unknown |

The four completed baselines have identical counted work but walls spanning 42.364–59.986 s. Pool-only is slower in its first complete pair and faster in its third; the other baseline is censored. Combo reduces observed work in the two complete pairs, but still returns unknown. Neither observation is a proof-performance win or a gate pass.

## Per-law results and targets

[**All 300 per-law observations: `per-law.csv`**](per-law.csv) gives each generated statement's name, verdict, attempt count, completed-attempt count, normalized units, completeness flag, and wall time (`wall_ms`). [`summary.json`](summary.json) contains the per-run profiles and all 312 law draws.

All twelve processes generated the **same 25-law family**, byte-identical in the recorded law JSON (SHA-256 `d8dac592168ff2d5e6dd4d94f498b30a637479480cb4b902e66745d0301e842c`). All have the same observed outcome partition:

- 17 laws had at least one attempt return a proof object **under its current candidate context**. These are labelled `conditional-proof`, not independently proved laws; this accounting audit did not separately replay those proof objects.
- The following eight remain `unknown`:
  1. `one primary per term`
  2. `CT at most 44`
  3. `CV at most 2`
  4. `CfgT at most 44`
  5. `fields: St[a]=1 -> CT[a]=CT[b] -> CV[b]<=CV[a]`
  6. `fields: St[a]=1 -> CT[a]=CT[b] -> CfgT[b]<=CfgT[a]`
  7. `fields: St[a]=1 -> CfgT[a]=CfgT[b] -> CV[b]<=CV[a]`
  8. `every x with x < size: never Config[x] is 0 and 1 <= St[x]`
- **Zero checked/accepted complete families** in every run. A conditional proof is not promoted when its supporting family fails.
- **Inv2973: not generated, not attempted. Inv*: not generated, not attempted.** No conclusion about their closure follows. They were not added to make this original-harness run resemble a published-family replay.

For the actual caller, `one primary per term`, pool-only spent **19,953.405 / 15,669.836 / 19,991.439 units**, versus **14,377.621 units** in each completed baseline. Combo spent **18,517.364 / 17,387.773 / 15,657.435 units**. It remained unknown in every case. Costs sum over dispatches/context changes; they are not one dispatch's allocation.

For a process killed during a law, its incomplete final attempt is excluded from that law's numeric sum and `units_complete=false` marks the lower bound. Completed attempts earlier in a censored process remain actual observed work, not a completed full run for comparison. The two censored run totals are likewise labelled incomplete.

## Validation, provenance and custody

- Typecheck/lint: zero errors and warnings, both measurement setup and audit.
- Budget/AST-size tests: 3 pass, 99 assertions.
- Independent audit: all **312 law draws** and **489 fallback draws** satisfy the recorded proportional/one-third formula; attempt ledgers and all six generated-family pairings match.
- Both passes keep one dispatch lease. No source/kernel proof rule, law generator, or allowance outside the research copies was changed.
- Prepared bundle hashes and the complete core/kernel allowlist audit: [`../section17-pooled-v1/integrity.json`](../section17-pooled-v1/integrity.json). Kernel is identical in all three.
- Raw journals, prepared bundles, policy patches, measurements and logs are in the SHA-verified [`../section17-pooled-v1/receipts.br`](../section17-pooled-v1/receipts.br), checksum `ae7185f9baa38ec537cbe362bf0fcb6b1fbca9766fdedb725c23f0e263838c95`. Measurement log and placement are beside it.
- The audited summary/CSV archive is [`receipts.br`](receipts.br), checksum `8b3fdb8f7b8c2c5ca9c54cf8dc7b904999a0cd699348aa6e2268a715c7ca6753`. Audit log: [`../section17-audit-v2/audit.log`](../section17-audit-v2/audit.log).

All jobs exited. Remote temporary outputs and transfer chunks were removed only after checksum verification; prepared shared caches were left alone.

**Decision:** this prototype redistributes work but closes no additional law or production goal. Keep it research-only. No next protocol was run.
