# Generic retained source lift

`emitGenericLift(capsuleDirectory, sourceFile, outputDirectory, options?)` is the
synchronous product entry point (`index.ts`, re-exported by the public facade).
It emits a fresh Lean project and `EMITTED.json`. It never executes Lean, searches
for proofs, loads a protocol registry, evaluates source code, or issues a checked
receipt. The status is always **EMITTED_NOT_CHECKED**.

Shared orchestration helpers are exported: `readLiftInput` validates data and
hashes without asserting source equality or restoring terms; `generateGenericLift`
checks the generic source/shape and generates `{project, manifest}` after the caller
has restored terms; `writeLiftProject` validates the manifest hashes and writes
only an unchecked emission. Legacy `final29-native-certificate/v1` envelopes are
explicitly unsupported here, not recast as native capsules.

Run once in a **fresh process**. Restoring the capsule's process-local term table
is single-use, including failed attempts. Errors after restoration require a new
process; do not retry in the same worker.

## Data-only source ABI

```json
{"schema":"gdp-lift-source/v1","id":"output_name","machine":{},"laws":[]}
```

Supply an actual `Machine` and nonempty `Law[]`. The example only shows the envelope.
`id` is naming-only: generated theorems retain `bapa_<id>_...`; it never selects a
route. IDs are ASCII identifiers beginning with a letter, at most 75 characters
(the established generated-identifier bound is 80 including `bapa_`). Unsafe IDs
are rejected, not sanitized or merged. The entire machine, every law, and their
metadata must match `capsule.original`. Object key order is irrelevant and absent
optional members equal `undefined`; no other values are erased or reconstructed.
Functions, accessors, sparse arrays, hidden/symbol metadata, cycles and non-JSON
numbers are refused. Nonempty function declarations are unsupported even if they
contain strings instead of JavaScript functions.

## Shape routing / scope

- Complete counted family plus source-count preservation / count augmentation:
  split counted bridge, including every retained family member and frontier.
- Retained witness/existential provenance: witness bridge, every parent and full
  family, actual original binders, and checked alpha-transport obligations.
- One ordinary retained family, exact or quantified/row-alpha machine: alpha
  bridge. Proposed renames remain obligations checked by the emitted Lean code.
- Other semantic transformations are explicitly unsupported. There is no search
  or special-file fallback and no dispatch using IDs.

This is the **24 generic** cases (10 alpha / 9 counted / 5 witness), **not all 27**.
The three separately qualified toy/client/SDL semantic transports are outside this
module. Those labels are scope documentation, not an ID registry: an otherwise
generic machine with such an ID still uses its actual shape.

## Integrity and limits

Existing `bapa-*` capsule/graph schemas, SHA-256 verification, explicit graph
limits and term metadata restoration are retained unchanged. Optional
`expectedManifestSha256` independently pins `CAPTURE.json`; without it the receipt
binds the exact manifest read but does not assert independent trust. `sourceSha256`
binds the supplied JSON bytes. `limits`, `parts` and `maxSourceBytes` may override
finite positive limits; project output is bounded as well.

The receipt includes `familyTheorem`, nonempty original-law `sourceTheorems`,
`requiredTheorems` (root file axiom requests only), file SHA-256s, source/capsule
hashes, and `leanExecuted:false`. External build/run/check custody belongs to the
parent facade/CLI, not this emitter. Imported split-part print requests are not
mixed into the root audit list, because cached `.olean` imports do not replay them.

All Lean source is obtained through the product `leanLibrary` / `leanProject`.
There are no product imports or file reads from the research tree.

## Tests

`bun test lean-kernel/lift/*.test.ts` includes shape/id independence, complete AST
and metadata mismatch refusal, unsupported shapes, JSON refusal, single-use
restoration, codec tampering and bounds, original binders, all witness parents,
and generic counted/alpha generation. The deterministic synthetic fixtures build
constant-contradiction certificates, never proof search. `smoke.ts` runs a single
real retained-capsule emission in a fresh process; no Lean is executed. Run these
on the remote supercomputer, not the local host; see `unit.jobs.json`.
