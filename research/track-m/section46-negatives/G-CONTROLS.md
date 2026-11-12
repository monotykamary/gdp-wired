# B native/controller G controls — source only

Production base: `b42a0d82441c6d7ec4db94f1ad9c763423fb5957`,
tree `542d24c2e8c2ff7946b6611f8ec654651ed8768a`, parent
`051d091b1a88a98c896ea4b9e3b3fc75b6bbd3c6`.

**0 B tests compiled or executed.** A's reported T344 10/10 result does not
transfer to this B child. Request one authorized software gate on the final B
commit; do not launch, retry, qualify or activate from this document.

## Preserved chain and boundaries

- Original B `76c35b98` replayed as `d5c37dc1`.
- Original B `a0d77117` replayed as `d49226b3`.
- Mechanical G7 migration: `3b68e671`; mapping in `G7-COMPATIBILITY.md`.
- Authorized finite public endpoint correction: `d75d4188`; same raw roots and
  assertions, `clock()+root/fullRate` replaces the rejected infinite endpoint.
- All original 35 cases and assertion lines are unchanged by these adaptations.
- New coverage is separate: **5 cohort + 4 native/public tests = 9**, total 44.

## Five 46.18 tests in `core/count-recipe-cohort.test.ts`

All use the real `runCountRecipeController`, global native `workLedger`, exact
raw arithmetic and explicit FULL-profile guards, not skips. Returned payload
labels in this file test scheduling only; they do not assert native acceptance.

| Case | Assertion | Sensitivity to 0fc/b8 (predicted, NOT executed) |
|---|---|---|
| B1 | Same paid live headroom, with/without widening: identical closure allotment, ordinary and strategy. Exact fixture-only precharge aligns the observed remaining work; it never changes the root or grants credit. | Old ordinary pending=23 dilutes the first closure cap below W/8. |
| B2 | Outside selected member with Q=3 has p=4; both formulas. Q=0 pure arithmetic edge has p=1 and grants no credit; nonmember/blocked/usable entries excluded. | Old outside cap uses the full widened pending set and falls below W/10 before new helper diagnostics are consulted. |
| B3 | Twenty unrelated widened members remain scheduling candidates but not allocation peers; unchanged Req and first selected member; both formulas. | Old first ordinary closure cap falls below W/8. |
| B4 | Widened member has p=2; actual paid work decreases every live ancestor's headroom by exactly that use; refusal is authenticated and uncharged, ticket terminal, no soft retry. | Old 22-member pending denominator fails the W/5 bound before diagnostic fields. |
| B5 | Trigger becomes terminal after first proposal attempt; the second recipe keeps its original allotment/remaining record, cumulative use grows, later member uses fresh Q excluding the held member. | Old first cap fails W/8; remaining assertions detect allotment resets and stale Q. |

The coarse numerical discriminators precede new allocation metadata assertions.
Only the Q=0 edge accesses the new pure helper through a typed namespace view;
missing exports do not prevent the old controller from loading. For a future
negative-baseline gate copy **only the cohort test file** onto 0fc or b8, preserve
FULL/unit fixture settings, and distinguish compile/import errors from actual
assertion RED. None is yet observed. These fixture constants are not measured
protocol costs or a b0/F policy.

## Four tests in `core/count-recipe-context-public.test.ts`

1. **G1 public native closure:** ordinary supporter of an unknown-only target has
   p=2 despite twenty unrelated widened members. Real ordinary proof production,
   scope capture/replay and final `checkCountedLaws`; only untrusted row proposal
   production/inventory are controlled.
2. **G2 changed context:** mutate model bytes at the real first closing event;
   the public structured fallback must emit typed fixed-inventory refusal, with
   one original attempt and no repeated construction. This is a controlled
   negative input, not a report of 29-protocol incidence.
3. **G2 terminal structured re-entry:** same context emits terminal/total recipe
   counts and exact snapshot delta, without new attempts, instances or fuel.
4. **Native positive:** a real accepted certificate emits neither context
   refusal nor structured re-entry and has zero diagnostic counter delta.

Every public entry supplies a finite counted deadline under its existing exact
raw root. No kernel, ledger, scope, replay or checker module/function is mocked.
The public suite controls only untrusted inventory/proposal production and must
run in its **own fresh Bun process**. The old acceptance suite also requires its
own process; neither may contaminate owner or cohort suites.

## One requested software gate, not yet authorized or launched

Run the four B files in separate fresh Bun processes, with FULL enabled and the
unit fixture weights. Use explicit Bun/process wall timeouts independently of
work endpoints. Retain per-file outcomes even on failures. Include whole-tree
TypeScript checking and lint/message checks on all new B commits and files.
The old N3 remains intentionally RED under flat funding; report its actual
assertion separately and never suppress it or label the flat path disjoint.

G3/46.19 constants and capture ordering remain on HOLD. No G3 policy was added.
No NEXT-PIN lock is changed; timed diagnostics still have no event observer.
