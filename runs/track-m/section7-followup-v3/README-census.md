# Section 7 follow-up — construction and leaf-check census

The measurement-only code is installed into disposable Linux snapshots.
Production `core/` and `kernel/` are unchanged. All jobs ran sequentially on
`bx_3kjzmmhv`, exclusive, eight pinned vCPUs, no co-tenants.

## (b) Inv2973 construction/traversal, one level deeper

The old T1 residual was 9.543 s. This fresh replay has 11.024 s in that same
exclusive category; the table is a new measurement, not a retroactive division
of the old number. Inv2973's counted work matches its control exactly.

| Exclusive residual category | Seconds |
|---|---:|
| `rowsAt`: arithmetic-row materialization outside search/transport | 6.003606 |
| Remaining `proveCountCases` / `selectedCase` control work | 4.633495 |
| Focused pool construction | 0.287378 |
| Count-goal construction (`mcGoal`) | 0.048612 |
| Field-case control | 0.028775 |
| Obligation construction | 0.014494 |
| Witness-flag seeding | 0.005499 |
| Instance seeds | 0.000301 |
| Other, source-view, finish bookkeeping | 0.001821 |
| **Total** | **11.023981** |

RowsAt is 54.46% of this residual; the still-coarse case-control category is
42.03%. It is explicitly residual control work, not all attributed to a
particular AST transform. Admission/transport, ordinary search, demand
proposals and legacy proposals are excluded. Nested inclusive site totals
must not be added to the exclusive table.

## (c) What the 489–490-hypothesis leaf checks actually contain

| Provenance | Hypotheses |
|---|---:|
| Underlying obligation, including seeded witness instances | 378 |
| Count-read proxy bindings | 20 |
| Non-frame count-instance disjunctions | 65 |
| Frame count-instance disjunctions | 26 |
| Explicit guard prefix, when present | 1 |
| **Total** | **489 or 490** |

Of the 378 obligation hypotheses, 341 mention generated count witnesses;
126 of those mention frame witnesses. Thus only 37 are witness-free before
the optional guard. Calling all 378 intrinsic protocol hypotheses would hide
the substantial witness-instantiation overhead. The 91 count clauses are
valid count-instance disjunctions, not 91 assumed good bounds.

Independent proved scalar cuts add **zero hypotheses** to this list. They
are supplied as path atoms. The audited checks have 0–23 region lemmas and
0–23 additional checked path atoms.

The historical T1 trace recorded 136 full-goal leaf checks, but no leaf
identities. That exact trace cannot be audited retroactively. This fresh
same-input profile records **120** such checks (114 at 490 hypotheses and 6
at 489), using **5.717 s** in the ordinary checker. No budget was increased
to force the old count. The small Inv* counted-work delta is reported below.

For exact `(goal hypotheses, ordered checked path, leaf certificate)` identity:
**88 distinct leaves; 32 checked twice**, hence **32 extra checks**. By physical
leaf object identity: 96 distinct objects; 24 used twice. These are separate
notions; certificate-only equality across different goals is not counted as
proof reuse. Full per-call hashes and provenance are in `Invstar-leaves.json`.

## Validation and artifacts

- All five control/profile verdicts agree (three checks, two incomplete).
- Counted work matches exactly for four laws; Inv* differs by +0.325569 units
  (about 0.0063%). No exact-trace-equivalence claim is made for Inv*.
- TypeScript, type-aware lint, five meter tests / 15 assertions pass.
- Both T3 two-hypothesis numeric cores independently replay through the kernel.
  This checks the arithmetic with assumed goods, not their source provability.
- The source target's positive conditional check and provenance sums validate.

`construction-leaves.log` contains complete gzip/base64 data receipts, avoiding
remote stdout truncation. `control.log` and `profile.log` are their decoded
forms. `results.json` combines them with T2/T3. `validation/verify.log` contains
the independent checks. Setup-only failures and the earlier truncated log are
not accepted scientific measurements.

Reproduce with `jobs-section7-refined.json`, then:

    bun research/track-m/unpack-section7-receipts.ts LOG OUTPUT_DIR
    bun research/track-m/extract-section7-followup.ts OUTPUT_DIR
    bun research/track-m/verify-section7-followup.ts OUTPUT_DIR

Mount the canonical fixture and v7 captures as described in `README-demand.md`.
Gate 1 and the implementation decision remain unchanged; no new gates ran.
