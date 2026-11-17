# Remaining Rust / Swift original fixture migration

Source-only proposal on 66505d364; no native run, compilation, typecheck or pass receipt. Central `core/laws.ts` and `core/native-law.ts` are the intended integration API. The original fixture tests, extract/replay counts, constructor tests, failure and broken-model cases are retained. No adapter changes. All native positives below require Main's run and review; a checked callback is not itself a source proof. The callback-only refusal expected on a complete journal is exactly `source translation unchecked: a source proof contains a law with no native interpretation`. An incomplete journal can return its own reason first; do not mask it.

## Approved 0.50.3 release cut

T3 approved an incremental cut: the16 rows without registered companions retain their original positive assertions and remain honestly unresolved known failures. They are deferred native feature breadth (enum, optional, answered-call, clock and crash families), not relabeled passes or accepted refusals. Do not expand native feature support merely to close them for0.50.3. The4 rows with candidate companions may be retired only after an exact documented refusal plus a genuine same-family registered positive or concrete replay is verified. A companion's presence alone is not acceptance; retain a row as unresolved if its required evidence fails. Swift Tally's original positive remains pending its crash-observation determination. No row has been dynamically admitted by this ledger.

There are 11 Rust and 9 Swift original positive callback claims, plus Swift Tally's negative invariant. Every row remains unverified until a native receipt. Three Rust rows have an equivalent registered companion in source (including the preexisting load companion); the new Swift Tally companion retains the original positive pending crash support. Thus 16 of 20 original positives lack a registered equivalent, and all 20 lack current verified native evidence. Names identify exact callbacks in the tests.

| Original assertion | Source-only disposition / remaining contract |
| --- | --- |
| Rust load preserves atomic value | Same dynamic-order source/property registered in independent companion with tamper and disabled controls; callback now asserts checked kernel proof plus exact unchecked refusal. Unexecuted. |
| Rust failed store preserves value | Original positive retained. Need actual failed-store observation and exact implication companion. |
| Rust load invalid ordering iff failed | Original positive retained. Need observed ordering and failure, both directions; invalid load may panic. |
| Rust store invalid ordering iff failed | Original positive retained. Need observed ordering and failure, both directions; invalid store may panic. |
| Rust successful store stores input | Original positive retained. Need actual converted argument, success and atomic state companion. |
| Rust Budget spent <= limit | Same original extraction now has registered `spent <= limit`; callback asserts checked kernel proof and exact unchecked refusal. Must verify invariant sampling and original replay. |
| Rust Budget lap at 255 wraps to 0 | Same original extraction registered `old(laps) == 255 implies laps == 0` on lap; callback asserts checked kernel proof and exact unchecked refusal; false-native lowering and disabled checks added. Must verify sampling and proof. |
| Rust Budget mark sets phase present to p | Original positive retained. Need Option presence and value plus actual argument native semantics; no raw rule-name alias. |
| Rust Job finish success implies old Running and result 2 | Original positive retained. Need observed enum/result/failure companion. |
| Rust Job start success and old hits < 1000 implies hits + 1 | Original positive retained. Need real atomic state, result and guard companion. |
| Rust inferred boundary old used <= cap implies used <= cap | Original positive retained including omitted yield and process-id answer replay. Actual Rust answered-call journal unavailable; cannot substitute request input as observed answer. |
| Swift Budget spent <= limit | Original positive retained. Same source has crashing spend and constructor precondition; child crash observation is unavailable, so a complete honest journal is not established. |
| Swift Budget lap at 255 wraps to 0 | Original positive retained. Same original extraction includes child crashes; need complete journal and exact method companion. |
| Swift Budget spend at 200 with n=100 fails | Original positive retained; deliberate overflow crash child has `nativeObservations.error` = `child native observation unavailable after crash`; exact public refusal remains to be established, with original concrete replay and same-family native positive before any T3 disposition. |
| Swift Budget advance from done fails | Original positive retained. Throws require actual failure observation; do not assume a throw has the same contract as a child crash. |
| Swift Budget successful advance returns 1 or 2 | Original positive retained. Needs observed result and enum, with failure guard. |
| Swift Limiter allowed implies counter[user] <= limit | Original positive retained; actual fake-store keyed observation and actual answered flags.limit are necessary. |
| Swift Limiter denial leaves counter[user] unchanged | Original positive retained; actual pre/post fake-store keyed observation necessary. |
| Swift Limiter denial makes denied[user] >= 1 | Original positive retained; actual keyed map observation necessary. |
| Swift Tally add from n <= cap keeps n <= cap | Original positive retained; same extraction now includes registered guarded native law. Actor overflow/crash may make journal incomplete; determine from native receipt before model-only disposition, and add relevant tamper/disabled controls. |
| Swift Tally unrestricted invariant | Original `.proven === false` retained: broken law, never label kernel-proven. |

`translationChecks > 0` prevents empty source replay from being counted as native success; it does not prove a rare antecedent was sampled. Request a targeted real lap-at-255 observation as further non-vacuity evidence. Existing replay and atomic interpreter loops are unchanged, not substitutes for source-law checks. Failure paths cannot be retired as T3 honest refusals unless the exact public refusal, checked original mathematical claim and concrete original replay are all asserted and a same-family registered public-positive companion exists. No unsupported row above is silently retired; Main owns any decision.

The prior unsafe draft is retained externally in `/tmp/bapa-0503-control/results/0503-fixtures-rs-swift-original-draft.patch`; do not apply it. No heavy commands or submissions were run. The worktree diverges from Main's integration; Main owns combining it with shared observation changes and native execution.
