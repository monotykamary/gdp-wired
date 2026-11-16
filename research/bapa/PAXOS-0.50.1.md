# Paxos in 0.50.1

## What is checked

The accepted capsule is `paxos-accepted-capsule/`. Its Lean proof sources are unchanged
from producer commit `4a390a1b46b4965042d839cae4de273bc93e0937`. The mandatory provenance
update `ef68e18e60b1555fe6d47c8dfc79ec0cf08b6dfa` additionally binds the recovered original
TypeScript port and `common.ts`; its superseding `SHA256SUMS` digest is
`b6fb06da57088b8c9c9a5434674b4a6d400b915ff654386070f803967b9e35de`.

`Bapa.PaxosEprLiteral.family_checked` proves the complete ordinary `checkCMachine`
gate for all 25 family entries and 50 start/step obligations. Its reported axioms
are exactly `propext` and `Quot.sound`.
`Bapa.PaxosEprLiteral.original_source_safety` proves the named atomic source's
public safety law for every `CReach` state; its reported axioms additionally include
`Classical.choice`. The final theorem has no size-64 premise and covers zero size.
The source's admission, initial-state, and reachability conditions remain intact.
This is encoded-source safety, not independent TLA equivalence or a claim about
every implementation of Paxos. MLDR remains bounded to size 64.

## Proof format and replay boundary

This is a Lean-source capsule, **not** an additional native data-only `lift` case.
The existing 27 native-data-only cases remain unchanged. The 0.50.1 release suite
adds a distinct Paxos source replay; `release-0501-report.ts` requires all 28 cases
to share one exact release commit and base implementation inventory. It invokes
the original strict 27-case audit and the separate Paxos audit; missing cases,
mixed commits, and widened claims are rejected.

The producer's accepted final resume checked 20 modules freshly and reused 94
source-/object-hash-bound modules. Earlier checks supply those dependencies.
The release replay uses an explicit, verified retained dependency closure and
freshly checks the literal family, global gate, tuple links, all 25 entry wrappers,
and final family/source composition. It is not reported as a clean source rebuild.
Cache inputs must match the original native export manifests as well as their
source and object digests. A success log or a newly observed object hash alone
is not sufficient provenance. No proof search is part of this replay.

The capsule's pinned `lakefile.lean` builds the `PaxosEprAccepted` root. Its full
110-module local import closure is present. Two archived ancillary modules,
`PaxosEprTargetExport` and `PaxosEprTargetIdentity`, reference the absent
`PaxosEprAdapterAudit`; they are not in that root's closure and are not advertised
as standalone build targets. The capsule README's self-contained description
refers to the final theorem closure, not every archived ancillary file. A clean
`lake build` may be attempted with the pinned toolchain; no clean-build success
is claimed by the retained acceptance record or this release procedure.

The capsule preserves its producer's kernel sources. `Kernel.lean` is identical
to the release root's kernel. The ordinary `checkCMachine` gate and `CReach`
semantics are unchanged, but four same-named helper modules differ from the
current root's F-family/extensions or certificate construction. Do not substitute
current-root helper objects into the capsule replay without checking compatibility.

## Source and historical evidence

The Lean atomic source, `source-machine.json`, `source-laws.json`, and `basis.json`
are present and manifest-bound. The exact historical TypeScript input now also ships
at `../protocols/ic3syn/p2-paxos-source-input.ts`, with its original digest
`3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76`.
It is byte-identical to the recorded original Git blob, not a replacement by the
current protocol model. The source port and its pinned `common.ts` are both bound
by the new capsule manifest. `PAXOS-SOURCE-PROVENANCE.md` records the recovery and
producer's successful five-artifact byte comparison. The release replay reruns the
hash-refusing exporter and requires the same five exact artifacts before checking
the Lean proof. No additional protocol's coverage is inferred from this source file.

`p2-paxos-accepted-results/` retains the producer's family/source acceptance records.
The earlier family-only `sourceAccepted: false` and nested `EMITTED_NOT_CHECKED`
labels remain historical stage observations; final acceptance is recorded by the
top-level `UNIFIED-STATUS` and final theorem log. They are not rewritten as if all
stages had been checked together. Binary caches and the complete historical
custody archive are external replay inputs, not part of the source capsule.

The public `BOAT-RECEIPT.json` changes four location labels only. Its original byte
hash and the public derivative are recorded in `RELEASE-PRIVACY-0.50.1.json`;
artifact hashes, native result codes, and cleanup facts are unchanged. Original
bytes also remain in the parent commit. Capsule sources and their manifest are
unchanged.

The historical tree-lane cancellation exception is retained verbatim at
`paxos-trees-results/cleanup-note.json` (digest
`60b2e00a8e20e53a3e334e40ddd178d535870409be62f4a4cca7ba6e6d0477a7`).
It is separate from the completed accepted final batch. Retaining the note does
not claim its pending controller acknowledgement was reconciled. It is not a
reason to stop or reap another lane's jobs.
