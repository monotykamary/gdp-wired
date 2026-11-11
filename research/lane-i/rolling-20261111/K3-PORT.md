# K3 deferral stage on B integration

Approved source: `c22420222bf4351d7b4922a550ecf0abd23a71e9`.
D source decision: `research/verify-all/k3-deferral-c2242022/{REPORT.md,GATE.json}`.
Parent I stage: `f29796eeb46995abe99842f3f661aeba7016dff5`.
Exact tested code/index tree: `d66e5d1ff1987748113c858011bd30a65af3af1e`.

The authenticated prerequisite delta carries row agreement/composition/symmetry,
explicit unchecked proposal metadata, stage tracing and composition helpers.
The optional minimizer helper is an ancestor dependency; both ancestor
`GDP_COUNT_MINIMIZE` dispatcher registrations are deliberately omitted. No
minimizer policy, cache, weight, checker or interpreter is enabled or replaced.
The only new production flag is existing `GDP_COUNT_ROW_DEFER_CHECKS=1`, behind
the existing counted strategy route.

Standalone row checks cannot defer. A composition-only proposal can omit the
intermediate row checks but carries unchecked metadata. Final native STEP and
INIT checking remains mandatory. Observers label proposal work untrusted.

## Local gate, not combined admission

Boat batch `20261111-071110-q1kwrq`:
- 26 row/native tests, 128 assertions.
- 16 tail/composition tests, 99 assertions.
- Type/lint: clean across 1,923 files.
- All 181 protected identities verified by each driver.

`results/K3-pilot/` retains native receipts. Final combined default-off28 and
full-family gates, D composition review and final-pin calibration remain
pending. This stage alone makes no new timing or W claim.
