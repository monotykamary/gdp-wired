# T-10A — the guarded inclusion closes the captured complement

**Pass in all three B repeats.** A/B/A/B/A/B on **bx_25xas5gt**, the calibrated
fresh large VM, exclusive with eight pinned vCPUs. No production files changed.

B adds exactly one ordinary count instance, `r$4 - r$16 <= 0`, with fresh witness
`s10$inclusion`. It extends the packet **after** the original search has captured
it, rather than changing that search. The original goal/certificate/path hash
must match the Section 9 packet. Ordinary `seedCountWitnessFlags`,
`countedObligations` and `mcGoal` generate the fresh witness's premises. Every old
hypothesis must remain; independent slices are reindexed by exact content. The
source projection is checked against the live closure for every old witness.

The already validated Section 9 SAT point is reused only for numeric selection,
and revalidated against the live numeric goal and path. It violates the new
inclusion. This avoids charging a second search merely to rediscover that given
point. A is the old complement diagnostic, including its model and four source
queries; **A and B are different diagnostics, not a full-pipeline speed ratio.**

| B operation | Core | Counted units, each repeat | Required limit |
|---|---:|---:|---:|
| source query | 5 | 13.494384 | core <= 8; units <= 30 |
| numeric re-query (including natural-case proposal) | 4 | 18.638819 | core <= 6; units <= 20 |
| whole checked branch | — | 33.221761 | <= 120 |

Admission retains all four necessary conditions: `op = 5` (two integer bounds),
`?committedQuorum = 1`, and **CT[i] < CfgT[j$]**. It is not an unconditional cut.
The unchanged kernel checks the source proof, numeric proof and conditional
branch, with 25 independent lemmas, in each fresh validation process (75 lemma
checks total). All 12 control-source models and 3 control-numeric models also
validate. `validation.jsonl` is the receipt.

| Diagnostic | Counted units, each repeat | Wall median / max |
|---|---:|---:|
| A: old complement gap | 227.664816 | 0.137 / 0.142 s |
| B: new checked inclusion | 33.221761 | 0.279 / 0.525 s |

B's lower counted work is **not** a wall improvement in this test. B3's wall is
almost twice B2's; wall variance remains material even on the new VM. Packet
regeneration walls are separate in `summary.json` (about 8.6–10.9 seconds).

TypeScript/type-aware lint pass. **39 tests / 261 assertions** pass. `receipts.br`
contains all six original JSON receipts, all six stderr files, summary and fresh
validation. `extract-section10-ta.ts` decodes it without reconstructing results.
Term-column definitions are retained and their structural IDs exactly restored
before fresh proof checks; those definitions add no hypotheses or trusted rules.

## Setup attempts (not falsification failures)

The earlier directories' logs and placement receipts are retained:
- v1: installer anchor whitespace error, before a test.
- v2: adding the witness before regeneration lost the target leaf; changed to
  observer-only extension of the exact original packet.
- setup-v3: diagnostic-runner TypeScript error.
- setup-v4: one B sanity run passed; not the three-repeat acceptance batch.
- v5: all six measurements passed, but fresh proof replay lacked the process's
  term table and correctly failed; fixed by retaining/restoring that table.
- v6: all measurements and fresh checks passed, but the remote 400 KB tail lost
  the first control artifact. Repeated unchanged using a single Brotli bundle.

No cap, total allowance, trusted rule or original family harness changed. This
is one branch proof, **not** a completed Inv* law or a Gate 1 result. The passing
falsification test permits the generic generator and T-9D implementation next.
