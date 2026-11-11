# Original MLDR — measured gap

Historical measured source: `db14ee14`, unchanged original protocol and laws.
Not a proof or a current exact-tree validation. All work units are UNCALIBRATED.

## End-to-end public proveRule results

| Allowance | Verdict | Search units | Sampling (`small`, exclusive) | Rule preflight (exclusive) | Guards | Proof queries |
|---:|---|---:|---:|---:|---:|---:|
| 15000000 | UNKNOWN: generation allowance exhausted | 4424579 | 3749042 | 674410 | 1127 | 0 |
| 150000000 | UNKNOWN: generation allowance exhausted | 38174787 | 37499250 | 674410 | 1127 | 0 |
| 1500000000 | UNKNOWN: generation allowance exhausted | 375674773 | 374999236 | 674410 | 1127 | 0 |

Protocol-law construction adds 20 units outside search in every run.
The `small` phase throws budget exhaustion; the public API returns unknown.
No completed candidate-bundle event is emitted. `found` lists supplied laws,
not proofs. Original A at 15M is also unknown: 4,424,769 search units.

## Handoff to A: generation endpoint

At 15M, sampling alone consumes 3,749,042 units. Including the separately
reported guard work, generation spends 3,750,169 (169 over 25% of the total).
The other 674,410 units are exclusive rule preflight before/around that tier.
Thus the entire pre-strategy path is 4,424,579 units, not merely 3.75M.
At 150M/1.5B, sampling consumes 37,499,250 / 374,999,236 units and still
never reaches a proof query. A larger allowance does not close the gap.
If the 25% endpoint is meant to include all generation/preflight, account for
the fixed preflight before granting the sampling tier, and ensure generation
can finish or return a sound usable partial candidate set. Do not call an
incomplete generated family a final proof or bypass original-model admission.

## Original safety obligation and step cases

All four supplied laws (`C0`, `Copied`, `Config` kind laws and `one primary
per term`) remain unproved end-to-end. The original safety obligation has
the following status at **each** tested allowance:

| Obligation/case | Verdict | Blocking tier | Measured case-proof units |
|---|---|---|---|
| one primary per term / init | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:pick | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:copy | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:start | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:update_terms | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:become_leader | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:reconfig | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |
| one primary per term / step:send_config | UNKNOWN, not reached | generation / small sampling | not incurred; no proof query |

## 15 selected structural obligations

The planner selected these descriptors before sampling stopped. Selection is
not a proof attempt. All have **UNKNOWN / not reached**, the same generation
blocker, and no attributable leaf-proof spend. No leaf-exhaustion claim is made.

| Selected obligation | Result |
|---|---|
| inX: no quorum canVote/1 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum canVote/2 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum canVote/3 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/1 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/2 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/3 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/4 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/5 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/6 | UNKNOWN; generation blocked before strategy query |
| inX: no quorum committedQuorum/7 | UNKNOWN; generation blocked before strategy query |
| inX: stored guard reconfigs/inS | UNKNOWN; generation blocked before strategy query |
| inX: stored guard reconfigs/inS or disabled/0 | UNKNOWN; generation blocked before strategy query |
| inX: stored guard reconfigs/inS or disabled/1 | UNKNOWN; generation blocked before strategy query |
| inX: stored guard reconfigs/inS or disabled/2 | UNKNOWN; generation blocked before strategy query |
| inX: stored guard reconfigs/inS or disabled/3 | UNKNOWN; generation blocked before strategy query |

Raw phase/event ledgers and exact hashes are in `results/receipts/`; the compact
projection is `results/audit.json`. See `RESULT.md` for the ranked owning lanes.
