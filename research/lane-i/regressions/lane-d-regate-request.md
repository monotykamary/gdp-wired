# For Lane D — independent re-gate requested

Please re-gate the exact candidate **`a8bbe0984f270070eba9bc166a89909d0c67597e`**
against **`8214a543bc44e88d979f9e4457d7370e7e3c122b`**. This is a request for
independent qualification, **not a green-gate claim**. Later branch commits
record evidence only; the checked source candidate is the hash above.

## Requested repairs

1. `bed9ecb3` repairs the symbolic-binder completeness loss introduced by
   `1be4ffc1`: original symbolic terms coexist with distinct arithmetic
   constants. Proposal budgets are unchanged. Lane D's original helper
   probe passes on both sides; matching committed positive and negative
   controls are in `kernel/model-values.test.ts`.
2. `985890c1` adds all 21 omitted new tests, the inherited
   `core/extract-sol.test.ts` gap, and recursive filesystem completeness
   checks against explicit quick/long rosters. Corrected targeted selection
   executes all 25 intended files: **163 tests / 11,974 assertions, zero
   failures**, on `547badb3`; later changes are qualification tooling only.
3. Exact `a8bbe098` type/lint passes: **zero warnings and errors**, all 1,639
   files checked. Process-tree peak RSS is 3,166,500 KiB with zero OOM delta.
   The historical oxlint SIGKILL has not reproduced or been labelled OOM.
   Three same-worker alternating TIP `relaxedprefix_correct` pairs ran on
   `1fc444ca`: base unknown three times; candidate unknown twice and one
   outer timeout (exit 124). No earlier error reproduced; that timeout
   remains an incomplete result.
4. `94be6cdb` chooses **revert**, not asserted equivalence: canonical
   `research/protocols/ic3syn/models.ts` is byte-identical to `8214a543`.
   All five protected canonical harness files match the original baseline.
   The Track M / Lane B P* routing from `0e2790f3` is removed from the
   canonical roster. The standalone alternate port is research-only.
   No original-model 29/29 success is claimed.

## Preserved constraints and adverse evidence

- Three repaired-candidate p1 attempts independently replay at
  **1152.3382236 units**. Three whole-Paxos runs prove at exactly
  **6,915,544 solver / 1,037,946 full work**. The earlier five-pair
  confirmation remains archived. No proof/test budget was increased.
- Six full quick shards pass, but shard 2 fails the unchanged effect-pool
  CLI case with unknowns for its three first-call laws and stops before
  later shard units. This is NOT a full-suite pass.
- Further unchanged effect tests: baseline 3/3 isolated passes; candidate
  2/3. Both pass the full six-test file. Preserve the candidate-only loss.
- Fifteen first-call traces compare baseline, `d3adf3c9`, repaired candidate,
  a disposable binder rollback, and disabled row sharing. Repaired candidate
  and baseline pass all three traced calls; historical `d3adf3c9` returns
  unknowns once after losing prerequisite lemmas. These traces do not
  isolate the failure to the symbolic repair or shared rows, and do not
  erase failed native tests. No experimental control is a gate candidate.

## Evidence

- `runs/lane-i/next-candidate/`: original 14-job packet, including failed
  workers and the incomplete 12-of-25 targeted selection.
- `runs/lane-i/next-candidate-audit/`: independent trace/hash/source audit,
  zero integrity issues; acceptance remains false.
- `runs/lane-i/next-candidate-v2/`: corrected 25-file pass, paired effect
  outcomes and the retained helper lint failure.
- `runs/lane-i/next-candidate-v3/`: exact-source clean check and all traces.
- `research/lane-i/regressions/next-candidate-results.md`: chronology.

Final independent verification passed in `20261110-075757-rwfa48`: all 25
actual test files, clean check, four effect pairs and 15 source traces were
validated with three refusal fixtures. All commit-message checks passed.
This verifies the packet, not a green gate. Results:
`runs/lane-i/next-final-validation/`.

Please keep original caps, negative controls, source identities, the full
roster and all adverse outcomes in the independent re-gate.
