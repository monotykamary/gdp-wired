# Checked tuple-key primitives (not a full certificate translator)

`RadixKeySyntax.lean` was compiled by Lean 4.34.0 through the axiom gate in
batch `20261115-225444-qkrs2t`, module log
`runs/bapa-transport/rekey-foundation-v2/rekey-foundation-compile.files/RadixKeySyntax.log`.
The module and `.olean` were exported. Every one of its seven printed theorem
axiom lists is a subset of `{propext, Classical.choice, Quot.sound}`.

Verified:
- unbounded raw-address universal iff a universal over two tuple components;
- the corresponding three-component equivalence;
- pair and triple equality iff component equality;
- explicit radix64 collision, and refusal of that collision by tuple encoding;
- seven parser controls: binary, flattened ternary and nested ternary packing;
  explicit raw-binder expansion; refusal of untyped and malformed raw binders;
  and literal-key conversion.

The batch itself exited nonzero **after** these successes: its final, unrelated
`BoundErasureCountedReplay` module was tested against the older sharded retained
kernel, which has no `CEntryF`/`checkCMachineF`. This is not a success for the
whole batch or for that counted module. The earlier unit revision failed on
reserved Lean identifiers; it is superseded and is not an acceptance receipt.

This checks only key parsing and abstract binder/equality lemmas. It does not
translate certificate tables, split rows, leaf rows, or full law instances.
No re-keyed family has been claimed. `SOURCE-BRIDGE-OBLIGATIONS.md` records the
additional, still-pending source obligations for every capsule.
