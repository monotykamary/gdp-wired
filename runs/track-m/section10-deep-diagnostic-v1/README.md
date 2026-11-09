# Exact attribution of the three proved-law increases

A: exact 50109a36. B: 192ebbe2. Same bx_25xas5gt, exclusive eight pinned vCPUs.
The diagnostic reproduces all Gate 1 counted totals. No timing ratio is claimed.
cost-attribution.json reconciles the weighted raw-counter differences exactly.

| Law | A | B | Difference | Focused instances |
|---|---:|---:|---:|---|
| one primary | 926.633492 | 947.543254 | 20.909762 | 22 -> 23 |
| Inv3915 | 872.335254 | 874.116294 | 1.781040 | 31 -> 32 |
| Inv1758 | 4310.475353 | 4312.612601 | 2.137248 | 31 -> 32 |

The new generator retains an existing full-pool inclusion: w$34, r$2<=r$7 for
one primary; w$61, r$5<=r$7 for the others. It adds four downstream hypotheses.
memberInclusions, focusCountCert and seedCountWitnessFlags themselves charge
zero counted units. This does not say they take zero wall time.

One primary: +20.693282 units in four SAT modelSequence queries, each 84->88
hypotheses; +0.216480 in grow, 167->171 hypotheses. Still 64 model-sequence calls
and 15 grow calls. The four deltas are 5.507892, 4.779232, 5.569398, 4.836760.
Raw differences include 44,127 extra scans, 1,402 value reads, 484 copies,
1,622 edges, 146 CDCL nodes and 834 goal nodes. No extra query count.

Inv3915: solely 905 extra goal nodes in grow, at 0.492/250 = 1.781040 units;
203->207 hypotheses. Inv1758: solely 1,086 extra goal nodes at the same weight
= 2.137248 units; 211->215 hypotheses. All per-call raw counters are retained.

No bound was pruned and no strategy, cap, total allowance or trusted rule was
changed. Full-family data here also establishes that its actual row draws are
much smaller than the separate 1,500-unit active-op-5 diagnostic.
