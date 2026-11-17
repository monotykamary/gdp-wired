# Rust / Swift source-only recovery — BLOCKED

This is a static handoff, not a native PASS. The exact original four-file diff is preserved outside tracked source at `/tmp/bapa-0503-control/results/0503-fixtures-rs-swift-original-draft.patch` (Git blob `f1f2d482876dc6118c74c967dc0cc0b97643a496`); it is an unsafe historical draft and must not be applied over the repaired source. Base: `cc61b35ea53ce0dd2509e5d1e6ca6235d8903513`. Reference shared API: `/tmp/gdp-bapa-0503-integration` at `b58234592` (not this base). No central, law, native-law, kernel, or policy edits made.

## History and evidence

The earlier committed migration is `a23371e613709da795dc80bdeea0072d923f362f` on `bapa/0502-source-finalization`; parent `0a9f1d3b5a5909c12d50cf8aba974e4cc0fa9b31`. It changes both original test files among many others, but is **not an ancestor** of either this lane HEAD or central `b58234592`. It expects the old exact refusal `native source replay journal was not recorded by this frontend`, whereas the current callback refusal is `source translation unchecked: a source proof contains a law with no native interpretation`. It has no per-case equivalent native companions; current reviewed policy therefore does not permit adopting it wholesale. The original tests in this lane remain unchanged. The prior committed changes are not lost and must not be confused with current integration history.

Original failed native diagnostics remain separate at `/tmp/bapa-release-0502-final-ae631359e/runs/admission-1/full-246/extract-rs.files/` and `.../extract-swift.files/`, with job receipts/placement in the containing run. See `/tmp/bapa-0503-control/results/failures.md` and `scripts/release-ci/known-failures.json`. These are failed earlier source snapshots, not evidence for this draft. No tests, builds, lint, native admissions or runs were made in this recovery; no owned new batch/waiter. All existing policy entries remain unchanged.

## Fixture ledger: original claims, all BLOCKED

The mathematical callbacks remain byte-for-byte in the current original tests. Each row requires an equivalent registered source-native positive with public proven+checked, sampled translation and nonzero checks, plus independent tamper and disabled-replay controls; absent that companion do not retire or relabel the old assertion. Names below identify the exact original claims rather than asserting that a proposed expression has been implemented.

| Fixture | Original assertion / guard retained | Disposition |
|---|---|---|
| Rust atomic ordering | load leaves value unchanged | Equivalent dynamic-order native companion and tamper/disabled controls drafted in `core/extract-rs.test.ts`; BLOCKED pending compilation, actual observations and native proof receipt |
| Rust atomic ordering | failed store leaves value unchanged | BLOCKED; actual failure and atomic observation |
| Rust atomic ordering | load invalid Release/AcqRel exactly equals failure | BLOCKED; native ordering binding and failure |
| Rust atomic ordering | store invalid Acquire/AcqRel exactly equals failure | BLOCKED; native ordering binding and failure |
| Rust atomic ordering | successful store retains supplied value | BLOCKED; actual binding and atomic observation |
| Rust Budget | spent <= limit invariant | BLOCKED; equivalent registered invariant |
| Rust Budget | lap at 255 wraps to 0 | BLOCKED; equivalent native lap rule |
| Rust Budget | mark sets phase to argument and present | BLOCKED; optional/enum native interpretation |
| Rust Job | successful finish implies old Running and result 2 | BLOCKED; native result/failure/enum observation |
| Rust Job | successful start with old hits < 1000 increments hits | BLOCKED; atomic observation and actual result |
| Rust inferred boundary | old used <= cap implies new used <= cap; std::process::id answer and omitted yield retained | BLOCKED; actual answered-call journal, no request stamping |
| Swift Budget | spent <= limit invariant | BLOCKED; equivalent registered invariant |
| Swift Budget | lap at 255 wraps to 0 | BLOCKED; equivalent native lap rule |
| Swift Budget | spend 200 + 100 fails | BLOCKED; crash journal and actual bindings |
| Swift Budget | advance from done fails | BLOCKED; crash/throw and enum handling |
| Swift Budget | successful advance returns 1 or 2 | BLOCKED; actual result and failure |
| Swift Limiter | allowed hit implies limit >= post counter[user] | BLOCKED; actual store, keyed read and actual flags.limit answer |
| Swift Limiter | denial leaves counter[user] unchanged | BLOCKED; actual store/key observation |
| Swift Limiter | denial gives denied[user] >= 1 | BLOCKED; actual keyed map observation |
| Swift Tally | add with old n <= cap maintains n <= cap | BLOCKED; equivalent registered native rule |
| Swift Tally negative | unrestricted invariant remains unproved | Original `proven:false` assertion preserved; never reclassify as model-only success |

Existing extraction request counts, inferred-boundary assertions, atomic interpreter order loops and broken/refusal cases remain untouched. Empty samples or checks all false are not native success. A separate Swift scalar set positive/tamper/disabled control was added, but it is not equivalent to any original retired fixture and does not close a ledger row. Controls are source-only, not executed.

## Repaired supported layer and remaining blockers

* The unsafe child pipe, receipt parser and parent preparation were removed. `core/swift/Main.swift` preserves fork/child crash isolation, waits only for its exact child and handles interrupted waits; on child crash `Harness.swift` explicitly returns `child native observation unavailable after crash` and unavailable bindings. No request-stamped substitute is constructed. Success re-executes in the parent as before and journals actual converted answered values from that execution. Fork/wait failure returns a harness error, not a fake crash. A crashing invocation cannot be source-checked. If child crash journals are later supported, they require a new bounded concurrently drained protocol with complete stale/partial/overflow and owned fd/PID handling.
* Rust root atomic state already uses `access(...).read` (SeqCst load); nested atomic capture now also uses actual load. Captured method arguments come from converted locals before invocation. Rust still has no actual answered-call or clock journal, so the inferred boundary remains blocked. Swift clock reads are not captured. Unsupported fake-dependency snapshots refuse rather than reconstruct fake state as actual getter values.
* Swift scalar answer journal records only actually called converted return values, detects differing repeats and reports unsupported values. Swift argument snapshots are captured inline, not via escaping closures or parent request preparation. Both harnesses advertise scalar-only equality. No object/container equality claim is made. These paths and the controls are static source drafts requiring compilation and adversarial native review; no execution is claimed.
* `core/extract-rs.test.ts` adds a registered equivalent of the original dynamic-order load state property and its false-native-lowering and disabled-replay controls. `core/extract-swift.test.ts` adds independent scalar argument positive/tamper/disabled controls. The originals remain unchanged. These controls are not a passed receipt and do not discharge any other row.
* Lane base `cc61b35ea` predates the observation reader (`3afd78daa`) and precedence repair (`b58234592`). Only Main integrates shared changes. C/JVM `e051d0095` is another lane's work and is not copied here; central's sixth native-law readings argument must be supplied in final integration by its owner. No edits to shared files are authorized here.

Next: review and compile generated source in Main-authorized native jobs, verify actual scalar/atomic and crash refusal controls, add same-claim companions with positive/tamper/disabled/non-vacuity controls for all remaining rows. Actual answer/clock support and keyed fake stores remain blocked. Unsupported constructs require the genuine exact refusal. Main owns all admissions and exact original commands.
