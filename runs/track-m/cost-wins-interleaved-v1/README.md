# Default-on cost wins: F1, F2, F3 and T-9C

## Engineering change

- **F1:** `proveCountCases` keeps standalone checking by default, and exposes an
  explicit pre-check deferral. `proveFocusedCounts` enables it automatically:
  its return is still an untrusted proposal, with the final transported
  certificate checked by the existing `checkMC` / `checkCountedLaws` callers.
- **F2:** slice leaf pre-checks to cited hypotheses and relocate every literal
  input, square and product offset. Keep all products. Fall back to the original
  full check if a slice cannot preserve an implicit row. Cache exact repeated
  leaf/path checks over the prover's immutable objects.
- **F3:** memoize successful independent-lemma checks by goal and lemma identity.
- **T-9C:** cache fully mapped retargets by lemma identity plus target slice and
  matched hypothesis text, not unrelated scope atoms or target-object identity.
  The text prevents equal slice vectors in different contexts from aliasing.
  Missing-hypothesis transports and root collection keep the original full
  scope-sensitive behavior. Failed computations are not memoized as successes.

All are generic/default-on; no protocol names, added proof allowance, changed
cap or modified trusted rule. `kernel/`, `core/counts.ts` and the existing
`research/track-m/profile-family.ts` are unchanged. `manifest.json` verifies the
entire kernel and original harness against **50109a36**. Only cache counters are
observed by a new wrapper, after each timed law result. `production.patch.gz`
is a losslessly compressed patch relative to 50109a36, including regression tests.

## Measurement

Exclusive **bx_3kjzmmhv**, eight pinned vCPUs. Six fresh processes:
**A1/B1/A2/B2/A3/B3**, same input and dependency pins. A is exact 50109a36;
B is the default-on candidate. The original per-law **5,000-unit / 60-second**
limits and final harness checks are unchanged. No later gate was run.

All **30 law results** have identical `(proven, checked)` verdicts across both
sides and all repeats: three checked, two unproved each time.

| Law | A counted units (repeat 1 / 2 / 3) | B counted units (repeat 1 / 2 / 3) |
|---|---|---|
| one primary | 926.633492 / 926.633492 / 926.633492 | same |
| Inv3915 | 872.335254 / 872.335254 / 872.335254 | same |
| Inv1758 | 4310.475353 / 4310.475353 / 4310.475353 | same |
| Inv2973 | 5002.653010 / 4837.597574 / 4882.748614 | 5002.653010 / 5002.653010 / 5002.653010 |
| Inv* | 5161.293823 / 5161.673620 / 5161.673620 | 3182.585646 / 5160.096021 / 5160.077578 |

| Law | A wall median / max | B wall median / max |
|---|---:|---:|
| one primary | 2.405 / 3.306 s | 1.968 / 2.967 s |
| Inv3915 | 3.445 / 5.582 s | 2.178 / 3.435 s |
| Inv1758 | 20.427 / 30.626 s | 12.497 / 15.252 s |
| Inv2973 | 60.226 / 60.529 s | 41.628 / 53.274 s |
| Inv* | 51.879 / 58.342 s | 34.046 / 60.036 s |

**Do not interpret the low B1 Inv* work as a saving:** it hits the wall limit at
60.036 s after only 3,182.586 units. A2/A3 Inv2973 also hit their wall limits
before reaching the counted limit. Existing cooperative deadlines can overrun
slightly; the measured work/walls are retained, not clipped. The fuller B2/B3
Inv* runs cost 5,160.096 / 5,160.078 units, essentially the baseline's work.

Family-process wall median/max is A **144.849 / 151.926 s**, B
**97.335 / 129.957 s**. B1 is slower than A1 overall. Median improvements are
not a uniform pairwise speedup, do not establish a stable speed ratio and do
not pass a 60-second all-proofs gate. In particular Inv2973 records no activity
in these conditional caches; its wall difference is not evidence of an F2/F3 win.

## Cache receipts (Inv* only)

| Counter | B1 (wall-truncated) | B2 | B3 |
|---|---:|---:|---:|
| Retarget hits / eligible lookups | 253 / 322 | **506 / 644** | **499 / 638** |
| Independent hits / lookups | 759 / 851 | **1495 / 1679** | **1495 / 1679** |
| Leaf checks / exact repeated-leaf hits | 80 / 20 | 160 / 36 | 160 / 36 |
| Full hypothesis total / sliced total | 39160 / 170 | 78320 / 342 | 78320 / 340 |
| Full-check fallbacks | 0 | 0 | 0 |

This is a real hitting retarget cache, not the old zero-hit identity/full-scope
key. It does **not** meet the earlier prediction of >=580 hits: the fuller runs
have 138 / 139 misses. The other four laws record zero conditional-cache calls.

## Validation and artifacts

Final static checks and **236 tests / 1,056 assertions** pass on the same
exclusive VM, including malformed certificates, expired deadlines, implicit
rows, scope changes, reordered targets, equal vectors with different contents,
and corruption of a final certificate after warming pre-check caches.
The independent receipt audit checks all six runs, all 30 verdicts, counters,
median/max calculations and kernel/harness identity. See
`../cost-wins-final-validation-v1/`.

`A1.log` ... `B3.log` are full per-law receipts; `measurements.json` is the joined
raw data, `summary.json` the runner summary, `audit.json` the independent audit.
No guard/generator/binding/budget work or later gate was included.
