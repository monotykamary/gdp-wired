# Upstream-component mutation result

Base: `66922371` (the owned private-read/source-race extension).
Measurement: boat batch `20261103-135726-rz229n`, logs in `runs/sec-real/final`.
Both workers used the same fingerprinted harness and 8,000 ms search budget.
No speedup or timing comparison is claimed.

| Pinned component | Clean policies proven | Generated mutants | Detected and source-replayed | Clean policies refuted |
| --- | ---: | ---: | ---: | ---: |
| AIlice `AGasTank` | 1/1 | 3 | 3/3 | 0/1 |
| codeAgent `IterationBudget` | 1/1 | 6 | 6/6 | 0/1 |
| **Total** | **2/2** | **9** | **9/9** | **0/2** |

- **Mutation recall: 9/9** for this selected cohort, not an ecosystem or CVE estimate.
- **False positives: 0/2** accepted clean policies, each proven.
- **11/11 source variants checked** for the declared public-callable surfaces.
- **9 witnesses, 18 independent source replays**, mutant plus original with identical inputs.
- Three operator families: guard removal, inversion and strict/non-strict boundaries.
- No production code, prover, kernel, defaults or public API changed in this stage.

Baseline sources and licenses remain byte-identical in `vendor/`. Temporary policy annotations are
checked for AST equality. Only recorded single-expression mutations change executable source.

## Coverage caveat, not hidden preprocessing

Initial default entry probes refused **9/9** candidates; see `admission.json`. Two became readable
with supported, explicit metadata:

- AIlice needs a type for unannotated `Consume.amount`; inputs still range over signed integers.
  Its policy concerns admission, not an invented nonnegative-gas invariant.
- codeAgent needs its three callable operations distinguished from three read-only properties.
  All state-changing operations are included; properties and `__repr__` are not request entries.

The other seven tested candidates remain refused, including constructor object/optional values,
string-valued maps and a filter callback. Sixteen additional inspected candidates were excluded
before reader probes, including missing/non-permissive licenses and external-service wrappers.
Those exclusions are recorded. Do not present this as “two arbitrary applications fully supported.”

These are real upstream components but a small, compatibility-selected sample. The original
projects are not alleged to contain these faults. Only local mutated copies were run.

## Validation

- Final two-worker measurement: zero failed jobs; every generated mutant included.
- `check` (TypeScript plus type-aware lint) and four structural/provenance tests passed in
  `20261103-135730-7yyb1r`.
- Six new tests, including a fresh measurement, independent 18-side saved replay, and commitlint
  passed in `20261103-140017-dygnes`.
- Registration checked across all seven shard plans: the suite occurs once, in shard 3.
- Affected shard 3 passed in the same final gate batch (three jobs, zero failures). Other shards
  passed at the base and were not rerun for this research-only addition.
- Exact upstream whitespace is preserved under a vendor-only Git whitespace attribute; authored
  harness and documentation retain normal whitespace checking.
