# Original-language native observations (0.50.3 repair)

A kernel proof of a translated reader rule is not by itself a checked proof of
the source. The existing `source-check.ts` admission checks remain unchanged.
In particular, a bare `rule.law` or `rule.stepLaw` callback has no independently
interpreted source meaning; it must not become a source proof merely because
its kernel formula proves. Reader tests using that form need genuine native
law syntax (`buildLaw`) or an explicit unsupported-law refusal test. A model-only
fixture is not a substitute for an end-to-end source-positive contract: each
retired model-only case must map to an equivalent registered-law native-positive
companion with public proven and checked, or remain blocked.

## Python adapter

As repaired in 0.50.5, the harness derives a signature from a fresh function
containing the actual candidate code/defaults, applies its defaults, and
snapshots the resulting arguments **before** invocation. For a wrapped callable,
the candidate must match the reader's source filename/name/first line. Its actual
entry frame must then execute with the same arguments and receiver; metadata
alone is never evidence of transparent forwarding.
It returns the existing bounded, identity-bearing native wire format. The host
uses one decoder for state and argument observations so real object identity is
not confused with value equality or symbolic map positions. Binding rows are
immediately frozen with the existing `nativeSnapshot`: the identity decoder
mutates its canonical objects on later frames, so retaining those raw objects
would corrupt earlier journal rows. The alias-history regression reuses the
same mutable input/state object across later frames, asserting historical
values remain separate while `nativeSame` still recognizes actual identity.

All Python source-state observations now use the harness's real object fields,
not just ordered containers. The former fallback reconstructed names like
`amount_` from the symbolic rule even when the original source field was
`amount`, causing a correctly enforced native law to fail or see a constructor
parameter instead of the actual state. No proof or translation acceptance
predicate is bypassed by this repair.

The Python wire encoder supports `None`, booleans, strings, whole numeric values
in the exact ±(2^53−1) range, lists, dictionaries with supported string/numeric
keys (not boolean keys), and objects whose selected fields are available through
`vars()` / `__dict__`, recursively within the existing node/identity bounds.
Actual datetimes, slot-only objects, bytes/tuples/sets without supported
`__dict__` observations, non-integral floats and unsafe integers are **not**
claimed as native observation support. A reader may still extract/replay such
code; a registered law demanding the unsupported observations must remain
`translation:unchecked`, `proven:false`, `checked:false` with the capture reason.
The nonordered-datetime regression requires this refusal on a real registered
step law and still requires its checked kernel proof; it does not fall back to
model timestamps or silently weaken native acceptance. That new control is
source-only pending the operational admission hold, not claimed verified.

Binding capture supports real Python functions and bound methods. The original
0.50.3 fence rejected all `__wrapped__` metadata; that regressed ordinary
`functools.wraps` methods and is repaired in 0.50.5. `__signature__` and
`__text_signature__` remain refused; wrapped chains are bounded, checked against
source identity, and admitted only after actual frame/argument validation.
Missing, repeated distinct, wrong-receiver or input-transforming entries fail
closed. Async resumption of the same frame does not count as another call.
This is an observation fence, not a claim that the frontend always refuses decorators:
`extract-step.ts` callFunc explicitly permits inferred transparent decorators
(~1173–1178) unless strict. `__text_signature__` is included because Python
inspect can consult it even without wrapper traversal. Native runtime defaults
from the genuine function remain authoritative; the omitted-None-default
control verifies a PArg `dflt`, an actually omitted native kwarg, and the
`apply_defaults()` binding from the native witness. A numeric default in the
original credit test alone did **not** establish omission coverage. These new
metadata/default controls are likewise awaiting post-hold boat validation.

The mutable-alias regression exercises the exact adapter snapshot helper with
shared state/input native IDs across successive frames; it is a transport-unit
regression, not an assertion that a frontend aliasing program has been proven.

Unsupported snapshots (out-of-range integers, non-integral floats, unavailable
object fields, unsupported object kinds, bounds) still make the journal
incomplete and source admission `proven:false`, `checked:false`,
`translation:unchecked`, with the capture failure named in `why`. No symbolic
input or protocol envelope substitutes for missing native bindings. Explicitly
disabled replay remains refused. Tests retain a corrupted symbolic-law control
that must fail with a real native witness.

### 0.50.5 external-call observations and LiteLLM regression

The Python harness records scalar returned/raised outcomes only when a stated
external call actually executes. Missing calls remain absent, repeated outcomes
must agree in value and runtime type, and unsupported values or inconsistent
outcomes fail closed. A native invocation counter prevents stale observation
reuse. The stated FakeStore is observed through its actual dictionary, including
absence, not by rebuilding symbolic cells.

The four MaxIterations laws now have registered source text. The old committed
callback-only corpus results are historical model results and are not a source
admission shortcut. The real pinned upstream source, transparent wrapper
controls, and replay-equivalent deceptive wrappers are mandatory release tests.

## JVM scalar bindings

The JVM harness snapshots actual converted arguments immediately before
reflection invokes the real method. Names come from bytecode parameter metadata,
not the reader's symbolic input schema. The check compilation preserves this
metadata with javac `-parameters` / Kotlin `-java-parameters`.

Source-state observations are read independently through reflection from actual
fields in the original source paths, using the same bounded identity-bearing
wire transport as Python. Selected fields, nested user records, maps and lists
retain their actual values and aliases; atomics and Optional values report what
they currently hold. Unsupported runtime values fail observation explicitly,
never falling back to symbolic heap reconstruction. The constructor-parameter
collision test requires the field named in the source, not its renamed model
slot or a same-named constructor input.

The supported argument observation slice is null, booleans, strings, enum names,
characters, and exactly representable whole-number primitive wrappers. It does
not claim native interpretation of arbitrary records/collections. An unsupported
argument or prebuilt class without parameter-name metadata explicitly refuses
source-law admission (unchecked, checked:false); recompiling with parameter
metadata is the actionable fix for missing names. The prebuilt negative test
requires that exact missing-name reason **and** a successful kernel proof, so
it cannot pass on an unrelated parse, compile, infrastructure or solver error.

This adapter work does not register arbitrary builder laws, change trusted
checks, grant a new known-failure allowance, or certify a whole reader suite.
The initial known-failure ledger remains open until exact targeted native job
receipts establish each fixture's success/refusal individually.
