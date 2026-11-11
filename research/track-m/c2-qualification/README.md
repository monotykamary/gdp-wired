# C2 production qualification gates — PREPARE ONLY

Base: `b4da69cf4755fb806f588a9b2639bab494460fe9`. Consumer interface: A's **T309 current lease interface**, not the superseded T305 clock proposal. The committed meter, corrected section46, candidate identities, released profiles and 44/49 rosters are NOT supplied by this preparation. No corpus proof, timing observation, activation, cap change, or Lean result is claimed.

## Entrypoints

- `bun research/track-m/c2-qualification/run.ts MANIFEST OUTPUT` prepares both gates. One production attempt produces both receipts; prefer it over duplicate runs.
- `closure.ts` selects the production/native closure verdict.
- `half-cap.ts` selects the composed half-case verdict.
- All default to **NOT_RUN**. Execution additionally needs `--execute`, a bound manifest, its explicit GO/release hash, actual T309 exports, and independent coordinator authorization. The manifest field is a guard, **not a validator or substitute for D's complete release artifact**. I must verify the release against candidate/domain/model/flags/stage before launch. A user-created GO string grants nothing.
- Missing meter exports produce **NOT_RUN**. No clock, displayed remaining work, legacy fullWork, ratio-derived endpoint, direct-emitter harness or reconstructed19-family fallback is used.

`manifest.draft.json` is deliberately invalid. I supplies all identities, complete cleared-inheritance flags and a separate exact manifest for each authorized44/49 population. R1/G1/owned deferral/batching are not enabled by this preparation.

## Executed checks, when released

The protocol factory and **production proveRule** run inside `workLedger.withBudget` with a rational WorkAmount. Public search work is the manifest's original safe integer input, decoded once, never recovered from telemetry. Every generated candidate identity must match the ordered expected roster. Required closure and explicit excluded/nonproof entries must cover it; the half target remains required.

A closed-family observation is not itself certificate acceptance. Every required INIT/STEP packet is independently passed to native checkMC, followed by checkCountedLaws, in the same root grant. Exact closed-roster identity and packet coverage are required. C2 emitter and composer route observations must both be present. A proposed, stranded, deferred, declined or expired half cannot pass merely because a constructor returned data: the half-cap verdict depends on accepted composition and native family acceptance.

`core/count-operation-observation.ts` adds a passive, default-off begin/end bracket around the existing emitter call. It changes no options, ordering, checks or caps. The end bracket survives emitter exceptions. Snapshots and passive exact-slice callbacks identify the constructor by its actual scope ID, stable `op:<value>` key, root epoch and original rational allocation. Missing explicit slice metadata remains NOT_RUN; a legacy deadline cannot substitute. Work started before that exact scope fails. The callback does not allocate or authorize work, and is restored on exceptions.

First-attempt half completion must fit the observed case endpoint; every trace prefix must also fit active member/root endpoints. **Typed section46 retry/fuel events have not landed. Multiple replacement attempts remain NOT_RUN**, never inferred as retry success from BudgetExpired.phase. That branch requires the actual landed contract.

## Exact observations and artifacts

F/R/E comparison, weighted-vector reconstruction and deltas use BigInt fractions and decimal counter strings, with no epsilon. Require all26 expected keys and exact weight identity. Preserve sequence, epochs, refusals, releases and exceptions. Check F+R against every endpoint and effective E against their minimum. These checks **do not prove physical coverage, unique credit ownership, or absence of uninstrumented work**: M1–M5 stays separately NOT_RUN.

OUTPUT is a file receipt; stdout is a small summary. Every lease event is streamed to OUTPUT.lease-events.jsonl with a matching SHA-256; only 16 head/tail samples and case-boundary events remain in memory. This avoids retaining an atom-level trace on the proof worker. File-I/O failures cannot qualify as a successful run. An accepted family is separately written to OUTPUT.family.json using I's portable term-column capture, bound to this manifest and payload SHA. Artifact serialization is outside the production/native-check work window, explicitly labelled. It can support fresh-process replay on A's landed meter child. **Fresh-process replay is NOT_RUN here**; old19 artifacts and off-meter replay are not substitutes.

The external producer packet must still verify source/import closure, commit/tree and adapter/runtime/native identities, M1–M5 coverage, OFF/default controls, retained-C2-lemma/scope/guard/index/missing/corrupt/false-base/false-step native mutants, corrected46 reduced-premise rules, fresh-process replay and applicable Lean gates. Local unit controls are not that corpus/native mutant suite.

## Validation scope

Focused worker validation covers receipt controls, the no-manifest dry-run, strict TypeScript and exact type-aware oxlint. It does not invoke proveRule on a protocol. These sources are ported from prepare-only fba9f907; old validation receipts are deliberately not copied. A must supply the explicit LiftedWorkBudget through the landed scheduler/production adapter before exact half-cap qualification can run. No reconstruction from clock, public numeric allowance or remaining capacity is permitted. The new GDP_COUNT_C2_REPLAY option is default-off and jointly enables owned replacement deferral, pruning and replay. Actual qualification remains blocked on the sealed A child and an independently authorized release.
