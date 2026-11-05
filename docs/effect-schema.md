# Effect Schema kinds (0.47 draft)

`fromSchema` on `gdp-wired/effect` bridges an Effect 3.22.4 or 4.0.7 Schema to an ordinary, typed `Kind`.
Effect remains optional: neither the implementation nor emitted declarations import it. This is a **decoded-value
frontend**, not a Schema interpreter and not a proof of a decoder, encoder, transformation or class constructor.

```ts
import {Schema} from 'effect'
import {fromSchema} from 'gdp-wired/effect'
import {proveRule, rule} from 'gdp-wired'

const Count = fromSchema(Schema.Int.check(Schema.isBetween({minimum: 0, maximum: 100})))
const counter = rule('bounded counter').inputs({next: Count}).state({n: Count.from(0)})
  .step(({next}) => ({n: next}))
const verdict = proveRule(counter, [counter.law('within bound', ({n}) => n.atMost(100))])
// Require verdict.proven && verdict.checked, including the state's schema-kind law.
Count.report // inspect the contract, retained constraints and any losses
```

On Effect 3 the bounded schema is `Schema.Int.pipe(Schema.between(0, 100))`.

## Exactly what “exact” qualifies

The default is `{mode: 'exact'}`. Its runtime report is **`exact-on-decoded-closed-values`**, not “equivalent to
Schema acceptance on all JavaScript objects.” The domain is:

- safe mathematical integers from `Number.MIN_SAFE_INTEGER` to `Number.MAX_SAFE_INTEGER`, including the Schema's
  bounds/literals. Both pinned Effect versions use `Number.isSafeInteger`; fractions, NaN, infinities and ±2^53
  are refused. `-0` and `0` represent the same mathematical integer (not distinguished by `Object.is`);
- actual booleans and strings (not 0/1 as boolean inputs), and null where explicitly allowed;
- structural records with **exactly their declared own fields**, and tagged cases with exactly `_tag` and their
  active case's own fields. Missing required fields, extra fields and symbol fields are rejected, not stripped.
  Equality is structural, not prototype/identity equality. Effect's normal object parser can accept surplus
  fields or strip them: those objects are outside this explicitly smaller, closed-value contract.

Within this domain, supported schemas' encoding and decoding round-trip structurally; samples and `empty()` are
members of the same domain. A raw `encode`/`store`/`from` value is validated, not coerced. `make(value)` builds the
corresponding symbolic value through the checked store path. The DSL's `encodeInput` is a low-level `Raw` API:
TypeScript accepting a raw argument there is not schema validation; the kind validates it at runtime.

`report.model` is separate. `Str` interns strings and abstracts their lengths: its symbolic assignments may not
all be realizable strings, even when the runtime codec is exact. That reports **`overapproximation`** and every
report says `counterexamples: 'validate-with-schema'`. A solver witness is not automatically an accepted Schema
value or a real run. Decode/validate candidates and replay them before reporting a bug. No predicate is executed
as proof evidence; standard Effect constraint metadata is read declaratively, not arbitrary functions. Do not
forge or substitute the AST/standard filter identities and then treat it as an authenticated schema.

## Supported subset

| Schema | Symbolic value | Contract |
| --- | --- | --- |
| `Int`, intersected integer comparisons / `between` | `Int` | safe range, inclusive/exclusive bounds retained |
| safe integer literal(s) | `Int` | equality / finite union, no holes silently filled |
| `Boolean`, boolean literal(s) | `Bool` | literal restriction retained |
| string literal(s) | `Choice<...>` | labels preserved |
| `String` | `Str` | runtime exact; symbolic model overapproximates |
| required `Struct` (including empty structs) | object of symbolic fields | closed structural fields |
| distinct required `_tag` structs in a union | `Variant<...>` | exhaustive `match`, `is`, closed case payloads |
| single `TaggedStruct`, singleton union | object with `_tag: Choice<...>` | a record, **not** a Variant |
| `NullOr(X)` | `Maybe<...>` | null only; undefined is not silently accepted |
| nominal brands without new constraints | underlying value | brand predicates, if any, must still be modeled |

Comparisons may be combined in either order and with fractional thresholds around integer values. For example
`Int > -2.5` has minimum -2; `Int < 2.5` has maximum 2. This is an equivalent integer constraint, not a lossy
rounding of input values. Contradictory/empty domains are refused. All safe bounds appear in `report.constraints`.

## State preservation is a proof obligation

Input/parameter constraints become assumptions. State constraints instead become `Kind.invariant` laws, which
`proveRule` and `proveSteps` prove beside user laws. They are not trusted premises or implicit clamping.
`Count.from(101)` throws; a symbolic step that can write 101 fails the kind-law proof even if the user's law is
trivial. Compiled stepping by itself is not a per-step runtime validation guard: use the proof gate, and `decode`
rejects a state outside the runtime domain. Null/tagged inactive payload constraints are guarded by presence/tag,
so clearing a nullable/case value does not require meaningless inactive fields to satisfy a positive minimum.

## Approximation is opt-in and inspectable

```ts
const K = fromSchema(Schema.Struct({enabled: Schema.optional(Schema.Boolean)}), {mode: 'approximate'})
K.report.runtime // 'normalized', NOT exact
K.report.losses // [{path:'enabled', code:'optional-to-null', ...}, {code:'undefined-to-null', ...}]
K.decode('x', K.encode('x', {})) // {enabled: null}: missing and undefined normalized to null
```

Unknown refinements/checks (including custom predicates and regex constraints) default to `SchemaError` with a
`path` and `code`. Explicit approximate mode may drop such restrictions; every loss names the path and why.
It may also project a `Schema.Class` to its declared fields. That report says `projection`, not class equivalence:
the result is a plain structural value, not an instance; methods, constructor behavior and prototype are not modeled.
Additional class checks and field predicates are reported too. Defaults/transformations are not executed.

Approximate mode returns **`SchemaKind<unknown>`**, also when the options type may select approximation.
The report and raw codecs remain available, but symbolic fields/classes are not promised by a possibly narrowed
Schema.Type. Exact-mode types select representations from the structural `Encoded` shape (transforms are refused),
so a nominally branded String remains `Str`, while a branded literal remains `Choice`; this does not prove encoding.

A pure input-domain overapproximation can prove universal properties for its original subset, **if the steps and
observations correspond**. It cannot certify a candidate counterexample without validation. Normalization or
class projection additionally changes representation; their correspondence to application behavior is a separate
obligation. This API does not claim such a correspondence automatically, nor that sampling validates a proof.

## Refusals and next steps

Arrays/tuples, maps/sets, index signatures, arbitrary heterogeneous unions, fractional-number schemas,
transformations (including async/context-dependent ones), declarations, and standalone null/undefined are refused.
Approximate mode does not override these refusals. An array is not automatically a stateful list; a future collection
bridge needs explicit item/state semantics rather than a global `Raw`/list-engine change.

Exact optional/undefined support is deferred: the current DSL `Maybe` uses null in its `Writes` and runtime-value
typing. Preserve missing vs undefined vs null before enabling that bridge; this release does not change the DSL's
raw type engine to make a false exactness claim. In particular optional variant payloads are refused even in
approximate mode rather than partially normalized.

## Migration from 0.46

The old adapter returned `Kind<any>`, discarded many predicates/bounds, and collapsed missing, undefined and null.
This frontend deliberately removes those implicit promises:

1. All numeric symbolic values are **signed `Int`**, even a nonnegative Schema. Schema.Type is just `number`;
   TypeScript cannot infer a natural-number refinement from its runtime predicate. Migrate a handler from
   `.state({total: 0})` plus `total.plus(schemaNumber)` to `.state({total: int.from(0)})`, use signed `min`/`max`
   methods, and return `Int.of(0)` in a variant match. Do not cast `Int` to `Term` to hide the mismatch.
2. State initialized from a Schema must continue to conform; out-of-range transitions now fail the checked proof.
3. Unknown constraints require an explicit model or reviewed `mode: 'approximate'`; inspect all losses.
4. Optional/undefined and Class projections require that same opt-in. Exact `NullOr` no longer accepts undefined.
5. A single tagged struct is a field object; only a multi-case union is a Variant. Type inference never promises
   raw numbers/booleans or class methods in symbolic callbacks.

See `examples/effect.ts`, `core/effect-schema.test.ts`, `core/effect-schema.types.ts` and
`scripts/smoke-effect-schema.sh` for both-version source, proof and packed-consumer checks.
