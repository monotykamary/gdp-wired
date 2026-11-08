# Section 10, step 1 — replacement VM calibration

Old VM **bx_3kjzmmhv** was idle and had no active owner when its exact ID was
appended to the scheduler's explicit-retirement file. Other IDs were preserved.
The scheduler released its lease; retirement prevents new placement or adoption.
No other client's VM was stopped. See `retirement.json`.

The calibration received **one new large allocation**, **bx_25xas5gt**, exclusive
with eight pinned vCPUs (AMD Ryzen 9 9950X). This VM is to be used for the following
Section 10 work. `placement.json` is the placement receipt.

One uninstrumented **census control**, as requested: exact 50109a36 core/kernel,
current unchanged census harness, same canonical fixture, 5,000-unit and
60-second per-law limits. This is one calibration sample, not a median.

| Law | Original census wall | v7 family wall | Fresh census wall | Fresh counted units |
|---|---:|---:|---:|---:|
| one primary | 1.963 s | 2.716 s | 2.029 s | 926.633492 |
| Inv3915 | 2.323 s | 2.885 s | 2.488 s | 872.335254 |
| Inv1758 | 11.604 s | 13.413 s | 12.179 s | 4310.475353 |
| Inv2973 | 24.619 s | 32.069 s | 25.327 s | 5002.653010 |
| Inv* | 29.282 s | 35.274 s | 29.857 s | 5161.392998 |

All five verdicts match: the first three checked; the last two unproved. Counted
work on the checked laws is exact. This control does **not** show the severe
slowdown seen on the old VM: Inv2973/Inv* are about 2.9%/2.0% above the original
census walls and below v7's family walls. One sample does not establish future
wall stability.

`census-control.log`, `environment.txt` and `summary.json` retain the control.
Historical comparison sources: `closure-phase-census-v1/candidate-focused-control-*.json`
and `closure-gate-family-v7/five-law-family.log`. No production changes.
