# Request quotient on the gated release integration

> Q1 qualification (subsequent D review): the historical 5e52d5ee oracle below
> counted every caught non-budget exception as a refusal. Its 301,348 throws
> were therefore unclassified, not demonstrated semantic refusals. They remain
> recorded below without being deleted. A separately authorized strict rerun,
> with source-branded guard refusals and fail-closed error controls, is complete:
> all 301,348 are authenticated guard refusals, zero unexpected. See
> `Q1-STRICT.md`; old evidence is not rewritten. Runtime bfe647cf is unchanged.

**Runtime source:** `bfe647cfd3b81e10c497ca4d5911a8097a02586b`.
**Parent:** D-scoped-GREEN `4c1c05dc` / runtime `2de2ce89`.
**Status:** all local source, compatibility, timing, Q1 oracle and static gates pass.
Staged for lane D; composition approval and fresh calibration remain pending.

## Delivered

An opt-in generic read-set quotient (`GDP_REQUEST_QUOTIENT=1`) in three files:
`core/request-quotient.ts`, `core/exists.ts`, `core/request-quotient.test.ts`.
Runtime/test diff: 265 insertions, one deletion. No checker, Lean, interpreter,
weight or production-rejection change. Defaults stay unchanged.

The sampler retains the original request order, logical work decrement,
first-success witness and random walks. It covers a class only after a
successful member. Refusals are not generalized. The structural argument and
checked dependency-calculus/fresh-key theorems are in `SOUNDNESS.md` and
`ReadSet.lean`; this is not a mechanically verified TypeScript translation.

## Request classes

The original MLDR domain has 36,288 requests; the quotient has **1,800 classes**:

| selector | retained input names | classes |
|---|---|---:|
| pick | i, S | 24 |
| copy | i | 3 |
| start | i | 3 |
| update_terms | i, j | 9 |
| become_leader | i, S | 24 |
| reconfig | i, hx, hy, S, Q2 | 1,728 |
| send_config | i, j | 9 |

This is a class count, **not** a claim that only 1,800 physical calls occur:
failed representatives are retried, and walks remain unmodified.

## Required same-VM ABBA timing

Batch `20261111-063416-hjj7er`, VM `bx_hep79j25`: exclusive **xlarge, AMD Ryzen 9
9950X 16-Core Processor, 8 of 16 vCPUs pinned, zero co-tenants**. Source archive
is the exact runtime pin; fresh child processes run A/B/B/A on that one VM.
`results/timing-9950x/placement.json` records the hardware.

| phase | A1 off | B1 on | B2 on | A2 off | off mean → on mean |
|---|---:|---:|---:|---:|---:|
| sampling | 4,089.04 ms | 2,660.73 ms | 2,827.70 ms | 3,947.40 ms | 4,018.22 → 2,744.22 ms |
| admission-prefix generation | 5,932.70 ms | 4,329.15 ms | 4,312.01 ms | 6,554.06 ms | **6,243.38 → 4,320.58 ms** |

Generation improves **30.80%** in this paired measurement; both quotient runs
are below six seconds. The prefix includes the native refutation preflight,
automatic kind laws, guards, samples and candidate construction, and stops
before any proof query. All four runs have **43 identical candidates**, including
order/hash; all sample digests agree (32 states at size 2, 1,504 at size 3).
An independent audit verifies these facts and ABBA placement/order.

Net provisional work: sampling **10,573,409.92 → 6,754,666.82**; generation
**36,731,970.10 → 32,913,227.00**. The equal 3,818,743.10-unit reductions show
that the saving is sampling work. Class setup itself costs **124,376 ticks**
and **10.77 / 13.53 ms** per measured setup; it is included in the net figures.

**Scope:** this is the current integrated source, not a re-timing of Fable's
older 49-law lane-B tree. The initial 45-candidate pilot omitted kind laws and
is retained as a narrower pilot, not the final ledger row. Neither this result
nor Fable's predicted rows establish an end-to-end 60-second MLDR proof.
The generation control has no whole-run work budget; its provisional work
exceeds 15M. No calibrated weights or W transfer are claimed.

## Census and compatibility

- **84 independently audited receipts:** 28 originals off/on/on repeat, each
  with 15M provisional units and zero forbidden clock reads.
- **10 checked proofs / 18 unknown**, unchanged. No refutations or lost proofs.
- All **8** candidate families captured before the baseline's cutoff have the
  identical ordered hash. Other originals either proved without generation or
  stopped before that boundary; no missing family is called equal.
- Every on repeat is identical after removing only timing/source labels.
- Every off receipt is identical to the gated release baseline after the same
  normalization. No release off-counter exception was needed.
- Maximum **15,001,010 units**, `paxos_epr`, unknown at `inference sample`:
  within the existing **1,024-unit slack**, with 14 units to spare.
- **28 legacy receipts** independently match the release baseline in verdict,
  candidates, events, queries and all 26 counters: **27 checked / 1 unknown**,
  all six added native counters zero. The legacy driver has no clock tripwire;
  the 84 full-mode receipts do.
- All five self-consistently rehashed corruption controls fail as required.

## Tests and final independent checks

The pilot passes **18 full-mode tests / 11,369 assertions**, plus **17 default
mode tests / 11,359 assertions** (one full-mode-only test skipped). Coverage
includes failed-first classes, all selector values, arithmetic/Boolean branches,
count bindings, bulk and one-cell writes, defaults, and the compiled-step
threshold. Direct endpoint tests stop class setup within 256 provisional tick
units. The standalone Lean proof passes without `sorry` or custom axioms.

Fable Q1 passes over **all 29 models / 49 parameter runs**. In disposable\nsource copies, the independent interpreter executed every one of **2,400,700\nskipped requests**: **2,099,352** produced the representative's identical\ncanonical successor, **301,348** refused, and none produced a distinct successor.\nAll off/on finite sample digests match. Eighteen models actually skip requests;\nthe others are checked vacuous/no-skip cases. This unmetered oracle is not a\ntiming or hard-budget receipt. Its independent summary binds every receipt to\nthe original sampler SHA-256 at `bfe647cf`.\n\nThe targeted follow-up checks **525** selector/target combinations for\n`add/sub/min/max/prod`, **3,366** concrete successors and **180** bulk defaults.\nIt includes plain-key, conditional-key and shifted-key writes, with an unread\ninput map adding key 100. All pass. Final whole-tree type/lint passes on\n**1,853 files**, including every new evidence script; both commit messages pass\ncommitlint. These checks change no runtime source.

## Retained failed attempts

Initial pilot test syntax and exhaustive-switch errors were repaired before the
successful pilot. The first Lean check only lacked the closing unnamed section.
The first explicit-budget generation control hit an existing local `finite law`
expiry before its huge endpoint; final generation uses the full counted clock
without a global budget. The first legacy audit incorrectly demanded a clock
field from the unchanged non-tripwire driver; the corrected audit requires the
same absent field as its baseline and changes no receipt. Failed logs and that
auditor's source are retained. The initial Q1 adapter failed parsing before any
oracle result; its corrected pilot and all-29 run pass. The final edge fixture
needed a non-null assertion for its bounded array index; that was a type-only
correction after its runtime tests passed. Final type/lint is clean.

Lane A was notified of the exact three owned files; production rejection and
refusal caching remain outside this change. D approval and fresh calibration
remain pending. No main merge or push; `.reflex-saved/` untouched.
