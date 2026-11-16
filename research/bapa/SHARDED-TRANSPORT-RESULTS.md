# Sharded KV retained tuple-certificate transport

## Checked result — not a family lift

Batch `20261115-232002-kxa1cm` (v5) compiled the complete generic translation
pipeline, original `Proofs`, target entrypoint, and generated `Checks.lean`.
Lean checked **25/46 obligations**:

- **All 23 initial obligations pass.**
- **Steps 0 and 9 pass.**
- **Steps 1–8 and 10–22 are rejected.**
- The full family check is **false**.
- The surviving-old-bound negative control is **rejected**.

`ShardedKvTupleChecks.lean` preserves the exact checked source, including its
negative family result. All three printed theorem axiom lists are
`[propext, Quot.sound]`. This proves the Boolean checker results, not safety of
the rejected family. Production/source bridging remains **PENDING**.

The runner's final native exit was 1 because its Python summary parser indexed
multiline diagnostic continuations as TSV rows, **after every Lean invocation
had exited 0**. The original metadata and artifacts remain untouched. The
parser is now restricted to three-column init/step/family rows. Do not resubmit
this completed admission to repair its reporting exit.

## Provenance

- Retained capsule: `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73`.
- Original Proofs SHA256: `c09073712bcf85986273c9c8e037e1e8174597fcea285aa5c9c21315cff78baa`.
- Receipt root: `runs/bapa-transport/sharded-tuple-v5/sharded-kv-tuple-certificate-replay.files/`.
- Original Proofs: 46.139s; target/diagnostics: 18.198s; Checks: 32.639s.
- No proof search, symbolic MLDR rerun, or local Lean was used.

The generic phases are `RadixBinderExpansion`, `RadixCertificateTable`,
`RadixTupleSyntax`, `RadixEqualityTree`, and `RadixCertificateTransport`.
Explicit layouts are Table0=(node,key), Owner1=(key,node),
TransferMsg2=(node,key,value). Complete kernel checking remains mandatory;
`RadixCertificateTransport.checked` requires the target family check.

## Current refusal boundary

`checks.tsv` records every obligation and the first rejected branch/row for
each rejected step. Every first failure has `named=true`, `table=true`, and
`arithmetic=true`: at least one submitted row is missing from the target's
actual premises. This is **not yet evidence of genuine dependence on 64**.
A separate diagnostics-only module imports the already-checked v5 artifacts
and compares actual target facts with transformed old hypotheses for steps
1–3. It does not repeat the completed family job or search for a new proof.
