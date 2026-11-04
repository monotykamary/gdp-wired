# New cold checker/source-replay contract

This is a separately authorized check of v3's saved bytes, not a rerun of its
prover/extractor and not a relabel of its frozen `final=false` verdict.

Acceptance requires all nine exact v3 documents to pass `checkDocument` under
v3's byte-pinned standalone checker closure, with each target law among accepted
claims. Metadata must match the exact full `meta.file`, entry, law name and expr.
Only then is `meta.where` compared to that same pinned file's basename plus exact
annotation line. A basename is never a file identity. Certificate kind is also
bound. Every claim result and before/after document hashes are retained.

A separate Python process reads the exact pinned negative CLI JSON. It accepts
only the full grammar `step(action=<canonical integer>)`, requires exactly
`0,-1,1,2`, and invokes `BrokenDrain.step` directly on the pinned pure source.
No eval is used. Initial and all four resulting states are retained, with final
phase 2 / inflight 1 required. This receipt replaces no historical flag and is
distinct from the earlier three-call finite probe.

All new packet input hashes and its manifest hash must match before/after. The
bootstrap copies only the frozen bundle into a fresh job-private stage and starts
the checker in a fresh process. No TypeScript package, node_modules, install,
network operation, prover, extraction, or certificate regeneration is needed.
The original requested budget remains 2 CPU / 4096 MiB / 60 s (native 30 s);
checker child ceiling 24 s clipped to a 27 s overall target, replay child 3 s
within the checker. No real-time guarantee or actual-supervisor claim follows.
