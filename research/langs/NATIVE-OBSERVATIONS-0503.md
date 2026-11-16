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

The harness binds the actual callable with `inspect.signature(fn).bind`, applies
its defaults, and snapshots the resulting arguments **before** invocation.
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

Unsupported snapshots (out-of-range integers, non-integral floats, unavailable
object fields, unsupported object kinds, bounds) still make the journal
incomplete and source admission `proven:false`, `checked:false`,
`translation:unchecked`, with the capture failure named in `why`. No symbolic
input or protocol envelope substitutes for missing native bindings. Explicitly
disabled replay remains refused. Tests retain a corrupted symbolic-law control
that must fail with a real native witness.

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
