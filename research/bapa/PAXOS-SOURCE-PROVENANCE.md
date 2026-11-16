# Exact Paxos source-port provenance

The accepted `sourcePortSha256` is
`3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76`.
The bytes now ship at `research/protocols/ic3syn/p2-paxos-source-input.ts`.
This is an exact copy, not an equivalent regeneration or an edited port.

Origin: commit `f6a5e18dc78f7dbdef23380f063ba94586943a65`, path
`research/protocols/ic3syn/models.ts` (bapa/p4). The Git blob at that revision,
p4's current file and `/tmp/p2-paxos-atomic-input/models.ts` all match the
accepted SHA256. The original source-boundary jobs copied
`atomic-source/models.ts` to the `p2-paxos-source-input.ts` alias inside the
remote job, but did not export or commit that alias. That omission caused
the release provenance gap.

The unchanged `p2-paxos-atomic-export.ts` refuses any other source hash and
also requires `common.ts` SHA256
`d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324`.
`p2-paxos-source-provenance.jobs.json` reruns that emitter from the tracked
source, with no scratch/input mount. It compares all four emitted artifacts
AND `SOURCE-EMISSION.json` byte for byte with `paxos-accepted-capsule/`.
This does not change any certificate, emitted definition, or accepted theorem.
Results are retained in `p2-paxos-source-provenance-results/`.
Batch `20261116-091127-ky3xb1` passed all five byte comparisons and commitlint;
its native exit code is 0 and `cleanup_complete` is true.
The capsule manifest now also binds the shipping source port and `common.ts`.
