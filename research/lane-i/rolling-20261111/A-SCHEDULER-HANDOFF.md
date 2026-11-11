# A owns the prerequisite-first scheduler — current I prototype handoff

CRITICAL section40 update: the necessary five-law SCC is real. A marks the
singleton prototype f1b8ebe8 NOT STAGEABLE despite passing control tests.
No commit/D request exists. A alone will implement joint SCC scheduling and
exact-scope invalidation, replacing destructive cycle/ordinary-failure
cascades. I stays frozen; all f1b8/T261/T262 results below are controls ONLY.

Latest A status (still NOT admitted/integrated): runtime f1b8ebe8, test-only
7f64ab72. T261 reports87 bit-identical census pairs (three29 groups) and
public mutation controls11/63, graph/commitlint pass; full native fixture
closes after separating read-only shape inventory from proof premises.
MLDR's15M census does NOT reach the scheduler, so it is not production225M
scheduling coverage. Three legacy full-mode failures are baseline-compared;
T262 isolated/static gates and commit/D handoff remain pending. I keeps
core/counts.ts/reserve/publictest untouched and will consume only the gated
single A implementation, not reproduce its fixes.


No parallel scheduler will be built in I. Current core/counts.ts draft is
frozen for A to inspect/reuse; later integration must consume A's exact gated
delta. I continues only the separate G1/C2 source/native work under HOLD.

Baseline:51ee4018. Immutable data:/tmp/lane-i-scheduler-handoff/source.tar,
source.txt and scheduler.patch. The tree contains only five changed/new core
files: counts.ts, count-closing-budget.ts/test, count-closing-needs.ts/test.
No G1/C2 or public test changes are included. The source tree hash is in
source.txt. Previous pilots P1-P5 did NOT finish native original closure.

## Contracts

- CountStrategyProof/CountLawProof may carry premises:readonly string[]. It is
  untrusted metadata, never acceptance. recordCountStrategyPremises includes
  instantiated offered laws and every scalar law (kernel assumes scalars).
- scopeCountProof(m,owner,family,proof,until) validates actual certificate
  hypothesis references INCLUDING independent cut slices. Explicit metadata
  may add premises but may not omit actual referenced laws. Names must exist
  and be unique. It records each premise as {name,key}, where key includes
  arity and strategyLawKey/formula identity; name-only reuse is not accepted.
- ScopedCountProof={owner,premises,proof,sources,unused}. replayScopedCountProof
  checks current identities, removes unused tuples, reindexes original rows,
  and normally checks each current goal. With explicit deferToClosing AND an
  originally unchecked proof AND full final deferral, it retains unchecked
  metadata rather than claiming acceptance. Final family check remains native.
- countClosingNeeds(callers,scopes) follows only scopes' cited names transitively
  through a deterministic Set; self/cross cycles terminate and missing names
  remain demanded. It is scheduling only and never certifies the cycle.

## Current prototype behavior / known gaps

It creates scopes only AFTER a proposal returns. neededForSearch additionally
seeds all successfully scoped selected strategies so their missing prerequisites
can be discovered before the caller has a proof. It prioritizes these names in
the remaining ordinary list, focuses per-attempt shares on pending required
members, tries a reduced context with full-context fallback, and early closes
only when every caller-transitive member has a proof+scope. These heuristics are
not A's requested general prerequisite-first graph and do not hard-decline a
dependent immediately when a known prerequisite fails. Replace/refine them,
not duplicate them. Cyclic/missing/expired evidence stays unknown.

Actual child withBudget protects the local search endpoint. Local expiry is
caught only when isLocalCountExpiration(error,closingBudget.until) allows it;
parent exhaustion must propagate. Final native gate executes after child scope
restoration at the unchanged root. A helper reserves3/8 of root W for final
native work,1/40 ordinary/INIT, old generation/strategy proportions as documented.
Root clamp is A's5258ba27; no fraction/price/root changes requested.

Known required order: Q2 and marker laws -> K3 fixture41 -> half law -> safety;
Inv* has recorded started/CfgT plus stored-guard/0 dependencies. K3 is not a
false/unneeded candidate. P4 row leaves already used ROW_DEFER, while added
DEFER affects F/G1. No flat cap/reject just to hide K3 cost.

Acceptance belongs to A/D: generic cited-premise scheduling, failed-prerequisite
refusal,225M unchanged root/37.5% reserve,29 census/28 other identities. I's pilot
receipts are diagnostics, not a GREEN or successful production closure. Native/
Lean discrepancy currently prohibits closure/promotion claims.
