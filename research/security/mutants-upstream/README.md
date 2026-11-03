# Mutation confidence on pinned upstream components

This separate cohort exercises code we did **not** write. It is not a CVE dataset and does not assert
that either upstream project has the injected defects. Only local copies are mutated; no upstream
service is contacted, exercised or changed by the benchmark.

## Sources and boundary

| Component | Pinned upstream file | License | Callable surface |
| --- | --- | --- | --- |
| AIlice gas tank | [AGas.py at 63a22105](https://github.com/myshell-ai/AIlice/blob/63a22105cdf8c0d297af332010f46e4153bbc1ec/ailice/common/AGas.py) | MIT, copyright 2023 stevenlu | `Set`, `Consume`, `Charge` |
| codeAgent iteration budget | [budget.py at e48780be](https://github.com/Harvil1/codeAgent/blob/e48780be52949dfcf17338025f6beab48ca01428/agent/budget.py) | MIT, copyright 2026 Harvil1 | `consume`, `refund`, `reset` |

`vendor/` holds the complete, byte-identical sources, their license texts, and AIlice's tiny exception
dependency at the same commit. `cases.json` pins every file by SHA-256. No implementation is adapted
or simplified. Temporary checked copies add only policy comments; Python AST equality verifies that
those comments do not change executable syntax.

The measured boundary is **all public callable operations**, not every property or display method.
codeAgent's `total`, `consumed`, and `remaining` are read-only `@property` descriptors, not callable
requests; its `__repr__` is not a request either. They remain in the original module but are not
separate checked operations. Preparation rejects a manifest that omits a public callable or hides a
property. Thus “fully read” means fully read for this declared callable surface, not unrestricted
whole-application coverage.

AIlice's unannotated `Consume.amount` is declared `int` in reader configuration; its unused
`resourceType` is retained so the source receives every argument. The integer domain is not narrowed
to nonnegative values. Both configurations keep exceptions as results. No calls are stubbed, no
operation is replaced by a model, no state-changing method is omitted, and no proof budget is tuned.

## Accepted policies

- **AIlice:** on `Consume`, `failed == (amount > old(gas))`. This checks rejection of an unaffordable
  request and acceptance at the boundary. It does **not** claim that `gas` is always nonnegative:
  the real `Set` and `Charge` APIs accept signed integers.
- **codeAgent:** `_consumed >= 0 && _consumed <= _total` after construction and every operation.
  The source clamps a negative total to zero and holds its real lock inside each operation.

These reviewer-stated policies reflect the source contract; they are not assertions that an
automatically proposed policy is the upstream author's complete security specification.

## Mutations and independent replay

`source.py` finds conditionals in public methods whose body rejects a call or changes a scalar field.
For every eligible guard it emits all applicable mutations: make a rejecting condition false or a
state-changing condition true, invert the condition, and swap a strict/non-strict comparison boundary.
Only one expression is replaced per mutant. Offsets are UTF-8 bytes, including after non-ASCII text;
tests include a non-BMP prefix. The operator does not inspect filenames, fixture IDs, policy names
or expected verdicts. Every generated mutant remains in the denominator.

The CLI uses a uniform **8,000 ms** search budget. Each broken-law run then executes independently
in Python on the real mutant and original class with identical constructor/method arguments. Replay
does not execute the proof model. Native locks and exception classes remain; the scalar observer
simply does not serialize lock objects. The shared concrete evaluator checks every applicable step.
Admission requires a proven clean policy, a checked mutant, and a violation in the mutant but not
its parent.

This is a sequential admission/invariant cohort, not a new concurrency benchmark. See the
[owned-source cohort](../mutants/README.md) for native concurrent source-race checks.

## Reproduce

Run CPU work on boat:

```sh
supercomputer run --jobs research/security/mutants-upstream/jobs.json --out runs/upstream-check --class gate --vm-type large
bun research/security/mutants-upstream/collect.ts runs/upstream-check
```

The second command only aggregates receipts. Worker-side validation commands are:

```sh
bun test research/security/mutants-upstream/upstream.test.ts
bun research/security/mutants-upstream/verify.ts
```

The suite is registered in `scripts/test-shards.ts`. It checks provenance, exact edit reconstruction,
generic operators, complete callable inventories, replay tampering and a fresh full measurement.
The saved verifier checks hashes and all 18 mutant/parent replays without invoking the prover.

## Selection bias and refusals

This is a small convenience sample selected for licensing and reader compatibility, **not** a random
sample. Selection preceded mutation measurement. `admission.json` retains nine initial reader
refusals, the two successful explicit configurations, and sixteen pre-reader exclusions (licensing,
external services, incompatible shape or no mutable logic). Unselected code is not silently counted
as supported. No ecosystem-compatibility or real-world vulnerability-recall claim follows.

See [RESULTS.md](RESULTS.md) and [measurement.json](measurement.json).
