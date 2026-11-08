# Isolated op-5 diagnostic — not the normal family allocation

192ebbe2, canonical input, bx_25xas5gt, exclusive eight pinned vCPUs. No strategy
or production source changed. Instrumented and original active probes have
exactly matching closure counted totals. ledger-summary.json checks accounting.

Inv*: first row a$#=i, j$=i. The scalar CT[i]<CfgT[j$] child checks; its complement
is unfinished. The terminal numeric query returns unknown/time. A separate
5,000-unit diagnostic allowance finds a validated model in 1115.639852 units,
violating 52 instances. Fresh sources: 6 checked refutations / 46 validated SAT.

Inv2973: first row a$#=i, b$=i. No scalar split is reached. The retained second
numeric model reproduces in 10.583062 units, violating 140 instances. Fresh
sources: 28 checked refutations / 112 validated SAT. Neither test has unknown
fresh source results. These new queries do not extend or debit the row share.

star.json / overlap.json retain paths, goals, term definitions and models.
star-sources.md / overlap-sources.md list EVERY violated instance, expression,
unit, source result and counted units.

| Non-overlapping work | Units | SAT | Checked | Reused | Unknown |
|---|---:|---:|---:|---:|---:|
| Inv* unsplit parent | 645.159893 | 11 | 13 | 33 | 17 |
| Inv* scalar yes | 17.071888 | 0 | 0 | 0 | 0 |
| Inv* scalar no | 837.799287 | 5 | 2 | 6 | 3 |
| Inv2973 first row | 1503.793922 | 14 | 25 | 55 | 32 |

Inv* totals 1500.031068, including 0.031068 atomic overshoot. Inv2973 overshoots
by 3.793922. These are measured stop-boundary overshoots, not additional draws.
Inv* has 35 raw arithmetic refutations versus 15 accepted source results;
Inv2973 has 56 raw refutations versus 25 accepted results. Do not equate a raw
arithmetic refutation with an admitted checked cut.

| Exclusive category | Inv* units | Inv2973 units |
|---|---:|---:|
| Natural-case arithmetic | 231.663167 | 226.135716 |
| Plain numeric queries | 464.648584 | 22.513826 |
| Batch-selection queries | 103.474256 | 221.423826 |
| Source queries | 692.602824 | 1023.551910 |
| Other source-attempt work | 7.642237 | 10.168644 |

## Important correction

These probes start op 5 with 5,000 units. Normal Gate 1 does NOT give op 5 this
allowance. The full-family confirmation in ../section10-deep-diagnostic-v1/
shows no row reaches 1,500: Inv* op 5 gets 124.647629 units; Inv2973's first op-0
row gets 71.362754. The isolated 1,500 cap is not the whole-family diagnosis.
Actual unresolved-family snapshots are retained separately.
