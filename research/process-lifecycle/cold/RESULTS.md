# Cold checker and exact source replay — accepted under the new contract

## Verdict and scope

**Accepted:** all nine exact saved v3 certificate documents passed `checkDocument`
in a fresh process, all returned claims passed, the exact four-call negative CLI
sequence was replayed on the pinned pure source and violated the invariant, and
all input/document hashes were unchanged before and after.

This is the newly authorized **cold checker/source-replay acceptance**, not a
relabel of v3. V3 remains `final=false`. No prover, extraction, or certificate
regeneration ran. No actual supervisor, OS signal behavior, locking, deadlines,
or delivery guarantees were implemented or tested. The platform premise remains
conditional as documented previously.

## Actual execution

| Field | Value |
|---|---|
| Batch | `20261104-112829-i4bxj3` |
| Uploaded tree | `a6a1e8ebd02f` (2051 files) |
| Image | `sc-f0d8daeee6c3` |
| Worker | **exit 0, 0.11 seconds** |
| Requested | 2 CPU / 4096 MiB / 60 seconds |
| Native limit | 30 seconds, from the previously pinned source conversion |
| Placement | `bx_85wyqdj5`, large, 2 allocated / 8 host vCPUs, nonexclusive |
| Native collection | 29.8 seconds wall; no fallback; zero charged starts |

Runtime/placement data are observations, not a benchmark or real-time guarantee.
No native submission-time spec or exact worker-binary attestation is inferred.

The cold manifest is
`47a281b5e673a0a1fb07a1ca1372990dd9b4aafa3d6fef1893e837d9c61cf938`.
It binds 27 files / 518,226 bytes: nine original documents, eight checker files,
two pure source files, v3 positive/negative JSON, v3 manifest/native receipt, and
the new runner/replay/contract files. The standalone closure was pinned to v3's
actual bytes. All eight also match the prior cold Sol closure; this equality is
corroboration only, not substitution.

## Certificate checks

The corrected contract checks the exact full `meta.file`, `entry`, law name and
expression against the pinned full-path source and its annotation. Only then is
`meta.where` checked against that same file's expected basename plus line number.
A basename alone never identifies the source. Certificate kind is bound too.

| Saved target law | Kernel document accepted | Returned claim results |
|---|---|---:|
| reaped has no in-flight signal | yes | 2/2 |
| lost owner invalidates authority | yes | 2/2 |
| lifecycle stays in domain | yes | 2/2 |
| no admission after retirement | yes | 5/5 |
| no admission after reap | yes | 5/5 |
| no admission after owner loss | yes | 5/5 |
| reap requires prior drain | yes | 5/5 |
| closed lifecycle cannot reopen | yes | 5/5 |
| authority cannot resurrect | yes | 5/5 |

All **36 per-document claim results** passed. This count includes repeated helper
claims; it is not 36 distinct target laws. Every document's before/after SHA256
matches the exact v3 bytes in the manifest. No document was rewritten.

## Actual exact negative source replay

The new Python process read the pinned negative CLI JSON, parsed only the fixed
integer-call grammar, required exactly `[0, -1, 1, 2]`, and called the pinned
`BrokenDrain.step` directly. It used no eval. Its exit was 0, with these actual
recorded states:

| Step | Call | phase | inflight |
|---:|---|---:|---:|
| 0 | initial | 0 | 0 |
| 1 | `step(action=0)` | 0 | 1 |
| 2 | `step(action=-1)` | 0 | 1 |
| 3 | `step(action=1)` | 1 | 1 |
| 4 | `step(action=2)` | **2** | **1** |

The final state violates `phase != 2 or inflight == 0`. This receipt is for the
exact four-call CLI sequence, separate from v3's three-call finite probe and not
an inference from the missing `replayed` flag.

Source before/after SHA256:
`142f3a3273e66bc36b0517aa0466d2ed43d6002f5b74296a094cc30b811a96eb`.
Negative CLI JSON before/after SHA256:
`348e9f3367b39a62f16e0351b5891d5ff37c1bd9a59a1cc49227d9837de84442`.
Raw replay stdout SHA256:
`57e4577c94025bee41b963a8001ae5bf6152977f8b4b27ce91f63b3c004891c5`.

## Retained evidence and preservation

Under `runs/astra-mac-lifecycle-cold/`:

- `bundle/manifest.json`, `freeze-receipt.json`: exact inputs, source origins and
  closure comparison; `bundle/certificates/` contains the nine unchanged documents.
- `results/`, `controller.log`: original native log, exit, placement and backend.
- `certificate-results.json`: every metadata verdict, claim result and document
  before/after SHA256.
- `exact-source-replay.json`: actual subprocess status, all five states, source and
  negative-input hashes, and original replay stdout.
- `events.json`: complete retained event stream, including all 27-file hash
  inventories before and after.
- `retained-report.json`: combined acceptance evidence. SHA256
  `c8d24b98830b85e29e10d4c36d6143c0f4bffd2fe05e57207007ac6aaee4ec63`.
- `native-receipt.json`: batch/tree and retained-output hashes. SHA256
  `4204faea76c6e21ce3e1175b8ce72ffb265e6a852d8b53296f86abd6c0860be4`.

Post-collection verification checked the complete cold input inventory and the
v1/v2/v3 receipt-bound files. All remain unchanged. No duplicate job, shared
node_modules change, provider mutation, real lifecycle signaling experiment, or
historical egraph modification occurred. The job-private stage was removed by
its creating bootstrap after the fresh checker process completed.
