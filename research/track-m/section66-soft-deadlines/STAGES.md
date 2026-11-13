# Section 66.8 stage inventory (base d5c442685f5c11394c1ac99fa0568647290b0344)

Source-only inventory. Tests are WRITTEN, NOT RUN. All source-native success checks remain in place; no kernel/Lean files change.

`withStageDeadline` is the full-accounting owned-endpoint boundary, legacy `withDeadline` otherwise. `withStageWall` preserves legacy wall behavior and delegates its existing counted endpoint to the owned boundary in a work scope. All 14 original explicit `withDeadline` call sites are replaced. There are also 7 supporting local call sites: two implicit counted stages and five local wall wrappers. Global/caller walls at `proveRuleWall` and from-any `proveStepsWall` are deliberately NOT soft.

## The 14 original explicit deadlines

Base line | Stage | Endpoint (unchanged) | Refusal / continuation
---|---|---|---
2980 | Quantified given-law preflight | clock()+ms/share inside existing counted(inferRates.work) | undefined report -> unproven/unchecked unknown -> searched
3091 | Recurrence/list discovery | until | no discovery result; continue without new lemmas
3098 | Cyclic function facts | until | no cyclic result; continue
3108 | Fresh-map laws | clock()+share | [] fresh laws; continue
3111 | Reprove given+fresh laws | clock()+share inside counted(fullRate,true) | no report; continue to inference
3120 | Existential cone | clock()+ms/2 | undefined; continue after the cone stage
3170 | Non-native support proof | end | undefined -> not proven -> drop support
3173 | Native fast support attempt | min(end,clock()+500) | undefined -> try local provenance
3175 | Native local support attempt | min(end,clock()+1000) | undefined -> try full support set
3176 | Native full support attempt | end | undefined -> not proven -> drop support
3184 | Warm native target/local cache | min(hUntil,clock()+3000) | undefined; no accepted result; continue to back()
3234 | Cone candidate proof | min(until,clock()+ms2) | {stuck:'unknown'}; never a proof
3262 | Liveness fresh-map laws | clock()+share | []; continue existing liveness stages
3300 | Decision proof with ms | clock()+opts.ms | {proven:false,checked:false,stuck:'unknown'}

## Supporting implicit/wall call sites

Base line | Stage | Endpoint (unchanged expression or previously polled ms) | Refusal
---|---|---|---
2979 | Given-law wall (including share=1) | countedSearchNow()+ms/share | undefined report -> search
3053 | Whole searchedUntil wall | countedSearchNow()+max(0,until-clock()) | original incoming verdict v
3077 | Bounded shallow/deep run allocation | clock()+ms inside existing counted(fullRate,true), same passed ms | undefined run; next search stage
3085 | k-induction allocation | clock()+ms inside existing counted(fullRate,true), same passed ms | undefined -> continue search
3120 | Existential cone wall mirror | countedSearchNow()+ms/2 | undefined -> continue search
3194 | Inference before reserved tail | tailAt() | undefined -> map-sum attempt then deep tail; diagnostic states deadline, not invented timing
3200 | Map-sum inference before tail | tailAt() | undefined -> deep tail

The bounded and k-induction additions make already-polled stage allocations explicit admission endpoints ONLY under full accounting. `withStageAllowance` calls the original body directly in legacy mode (no new legacy `withDeadline`); it changes neither the existing ms values nor counted rates. This can change measured work, including MLDR's run; no count parity or performance claim is made.

The cone's two existing broad catches now rethrow any remaining BudgetExpired. An owned refusal has already become the ordinary failure result; an error still escaping is not a cone-local success/failure to swallow.

## Exact ownership and failure policy

- The ledger creates a unique prospective endpoint identity even when entry refuses before the body opens. No failed-entry ID is reused.
- Ownership is classified at refusal, from the active ancestry and the ledger-authenticated error object; catch-time stacks and equal numeric endpoints are insufficient.
- The owned ID MUST be a limiting endpoint. Every other limiting endpoint must be a descendant DEADLINE mirror. Ancestor/root/scope/work-cap ties, stricter descendant limits, stale errors and other-ledger errors are not consumed.
- Genuine refusal stamps inner sticky guards. At the owning soft boundary it stops stamping ancestors; previously stored ancestor errors are untouched.
- The stage remembers its first local refusal so a checker that catches it cannot return accepted success.
- A separate pending-fatal slot records nonowned refusal. It wins over earlier local refusal even if body/inner guards catch and replace the later error. Tests introduce a smaller root after a rootless local stop, and a smaller inherited scope inside an existing root, without mutating ledger internals.
- The fallback runs only after endpoint unwind and guard removal. It does not receive new fuel. Its own errors propagate.
- Exact consumed counters, held reservations, root baseline/epoch and coefficient lattice are neither restored nor renewed. Normal endpoint lease invalidation/unwind remains the existing mechanism.
- Kernel/prove.ts, kernel/kernel.ts, the rest of kernel/, and lean-kernel/ are untouched. A fallback never fabricates a proven or checked result.

Residual unverified question: whether all 15 prior UNKNOWN cases improve. A stricter unowned descendant deadline still propagates by design; the new-pin gate is the evidence, not this source inventory.
