# Capture / cut-path memory successor (base 48f21567)

Status: source-only, no gate results yet. Main authorizes one focused boat test + strict compiler gate. The recovered 0e497x driver exit 137 does not establish who killed it or its RSS; no OOM-cause or measured-memory-improvement claim.

## 1. Collector output reuse — exact original work

Source48 already combines offered/inferred legacy capture. In `countedScopeHyps`, legacy `countedCertificateHyps` either reads sparse `leafRowsOf` metadata, or materializes the entire proposer table via `rowsAt`. The subsequent full native `leafConstraints` allocation duplicates that table.

For the latter case only, the supplier scan now reuses the already-materialized table. `reuseNativeScopeRows` executes the native builder's same funded atoms/facts, name discovery, same-map/equal-key comparisons, pair arithmetic, term closure, and naturality operations in the original order. It retains only initial atom/fact rows while doing so; generated output rows are discarded individually, not appended to a second full table. This saves a complete quadratic output allocation, **not quadratic arithmetic or counted work**. A sparse legacy leaf or evicted/missing proposer entry still takes the old single native build. A new read-only `cachedRowsAt` export in the untrusted `kernel/prove.ts` prevents a lookup miss from rebuilding/charging the proposer table; it never allocates or mutates cache state. No existing kernel/prover function body, checker, row cache, AST interning, row order, or supplier-closure precision is changed.

The work-only helper intentionally mirrors the unchanged kernel leafRows / sameKey / decide control flow. It uses the identical funded primitives, including native (not proposer) key arithmetic. Keep the paired reference tests when those native functions change. Capture runs outside the kernel's private `reusing` callback/recording scope, as before; this is not a public kernel row replacement. A row-count mismatch refuses rather than using an incomplete proposal.

## 2. Exact path-identity cache — transporter units may decrease, but no check removed

`conditional-check-cache.ts` no longer stores one JSON serialization of every cut atom per goal/tree/path. An exact per-goal prefix trie interns the ordered `(original key, holds, canon(lin))` word, and the leaf stores the terminal node identity. The atom vocabulary is shared per goal; common 580-cut prefixes share their nodes. Edges hold nodes weakly, and live terminal keys retain their ancestor chain. Dead trees do not force all historical path nodes to remain alive. No hash, lossy prefix, eviction-induced miss, or mutable-Path-object shortcut is used. Every lookup still executes the original per-atom `canon` calls, including cache hits; equivalent structural paths still hit and different order/key/holds/content still miss. False results remain cacheable.

This is bounded by the goal's distinct atom vocabulary and live cached paths, **not an absolute RSS cap**. Nothing invokes GC, clears other owners' caches, or installs an observer in production.

## 3. Protected behavior

Main explicitly rejected blanket self-check skipping because it moves repair-eligible case5 into case6/family rejection. **All transporter self-checks, collection checks, native count validation, final checkMC/checkCountedLaws, legacy extraction, hard-stop boundary, diagnostic stages, lazy supplier resolution, original instances, and shared retry bit remain unchanged.** No certificate is rewritten, no replay is added, and no producer is called. All existing `kernel/**` function bodies (the sole addition is read-only untrusted cache access), `count-proof-scope.ts`, `count-proof-rescope.ts`, `count-cert-transport.ts`, `conditional-proof.ts`, controller, counts, flags, root and weights are unchanged.

## 4. Planned single gate

Original seven focused files plus `core/count-scope-row-reuse.test.ts`, in one unfiltered Bun test invocation with FULL/shared rows; one strict compiler invocation even on test failure, including new helpers and test workers. The new test spawns isolated synthetic reference/reuse workers (not additional Bun test invocations or MLDR admissions) so both arms have identical cold and warm memo history. It compares native/proposer row bytes, exact ordered supplier sets and unchanged certificates, all per-event work counters/sites/reservations/refusal states, true/false cache hits/misses, and budget refusal prefixes. Fixtures include pairs, tuple keys, products/squares, duplicate suppliers, nested terms, all cut kinds, sparse metadata, forced 4096-entry eviction, and a 580-cut shared-prefix identity control. Frozen source48 collector and pre-check cache copies are test-only.

No test result yet. Full gate logs, source-before/after hashes, runtime identity, native result and strict close/cleanup must be retained. Send exact source/tree/patch and receipts to D, then Main inbox. No new MLDR admission is authorized by this implementation task.
