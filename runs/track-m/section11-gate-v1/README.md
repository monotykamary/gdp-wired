# Section 11: the two-defect repair, three interleaved repeats

A is exact 192ebbe2a1064aebf3d847cd044ad4ba948a5a32.
B production is 5974b9165d6860f1157f3bed3cd66a7e1514e904.
Order A1/B1/A2/B2/A3/B3; same bx_25xas5gt; exclusive eight pinned vCPUs.
Kernel, existing profile-family.ts, dependency versions and input are identical.
The manifest permits exactly the two implementation files and their two tests.
No other strategy, total allowance, row ceiling or later gate changed.

All 30 verdicts agree: one primary, Inv3915 and Inv1758 check; Inv2973 and Inv*
remain unproved. This is not a successful five-law/60-second gate.

## Counted units

| Law | A (each repeat) | B (repeats 1 / 2 / 3) |
|---|---:|---:|
| one primary | 947.543254 | 947.543254 each |
| Inv3915 | 874.116294 | 874.116294 each |
| Inv1758 | 4312.612601 | 4312.612601 each |
| Inv2973 | 5001.811726 | 5108.274084 each |
| Inv* | 5160.104960 | 5162.032223 / 5160.085453 / 5160.085453 |

The proved laws' counted work is identical. Inv2973's measured work increases
by 106.462359 units. Neither open law completes inside the unchanged allowance;
measured work can cross an atomic stop boundary. Inv* still has a small counted
variation; it is not presented as a stable counted-work saving.

## Wall seconds: median / maximum

| Law | A | B |
|---|---:|---:|
| one primary | 2.165 / 2.791 | 1.641 / 1.863 |
| Inv3915 | 2.817 / 3.100 | 2.019 / 2.222 |
| Inv1758 | 10.756 / 14.541 | 9.796 / 15.345 |
| Inv2973 | 24.756 / 35.721 | 27.954 / 29.729 |
| Inv* | 28.417 / 33.017 | 24.863 / 24.912 |
| five-law family | 68.881 / 89.173 | 67.214 / 72.299 |

Family A repeats: 89.173162 / 66.634933 / 68.881277 seconds.
Family B repeats: 72.298783 / 67.213715 / 61.566934 seconds.
Every B family is above 60 seconds. A1 and B1 show material warmup/host variance;
these numbers do not establish a stable speed ratio. Inv2973's median regresses.

## Correctness and the after-MLDR knob census

The regressions fail on the old implementation (../section11-red-v1/) and pass
on the fix (../section11-check-v1/). The empty-core test exercises the actual
numeric closure, not just a stand-alone proof helper, and checks its returned
tree with the unchanged kernel. The allocation tests assert even sharing,
remaining/3 as a ceiling, one parent deadline for children, and conservation of
spent plus unspent allowance. A last leaf does not get a budget windfall.

For the after-MLDR knob census: the unchanged literal at
core/count-recovery/row-cases.ts:103 is `Math.min(until, clock()+1500)`.
It originates in 616b0c9c (feat(counts): port guarded witness derivations to
production), with no adjacent derivation of 1,500. The separately corrected
leaf formula is min(remaining/max(1,leavesLeft), remaining/3).

## Evidence

All six complete raw logs, per-law records, manifest and summary are retained
in the checksum-bound receipts.br archive. First-unfinished-leaf diagnostics
for the two open laws are in ../section11-diagnostic-v2/. Final independent
raw-log/table, source-identity and model validation is in
../section11-validation-v2/. No diagnostic timing is mixed into these A/B walls. Final type/lint and 258
tests / 1,313 assertions pass; the independent auditor recomputes every table
from raw receipts, and fresh processes validate 120 source SAT models and
both diagnostic numeric models. Earlier audit-only failures are retained; no
timed A/B process was repeated.
