# T-9A final full-packet and SAT-model validation

Exclusive **bx_3kjzmmhv**, eight pinned vCPUs. Successful static checks and
**9 tests / 15 assertions**. No production files changed.

The fresh-process validator replays **12 records** (six strict and six
complement-only), independently checking **42 source SAT models** and
**14 numeric SAT models**, including all **56 original full paths**. It asserts
an empty opaque-column registry before each replay and uses `brokenOf` on the
exact recorded AST, not just the query's declared outcome or a scalar excerpt.

Every goal/certificate/path SHA-256 equals the original Section 8 T-A packet.
The full certificate, numeric goal, index mapping and all 24 active cuts also
match. For saved cuts only the redundant originalIndex debug annotation is
normalized away; its value is independently checked against the exact index
mapping. All proof-bearing cut data remain identical.

Strict test outcome: failed-or-inconsistent; **not a passing two-branch proof**.
Complement-only outcome: **generator-gap**, consistently across all three
repeats. Four positive-branch admissions are recorded, but no complete law is
claimed. No T-9B/C/D, production implementation or gate run followed.

Reproduce:

```
bun research/track-m/verify-section9-ta.ts \
  runs/track-m/section9-ta-v3 runs/track-m/section9-complement-v2 \
  runs/track-m/section8-ta-v3/Invstar-leaf.json
```

The full static/unit-test/replay command is in
`research/track-m/jobs-section9-validation.json`.
