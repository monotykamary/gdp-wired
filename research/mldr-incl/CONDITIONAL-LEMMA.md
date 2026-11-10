# Five-premise conditional inclusion — handoff to Lane B

**Not a safety proof, not a generated invariant, not a trusted fact.**
Production remains `0ee27c7a`; this follow-up changes research only.

The source is the immutable E-14 `stage-0.json` packet, SHA-256
`82a92edbc31b56ff7b295b31c9565846cf22b7c1828509aef68998d259bc6b1f`.
`runs/mldr-incl-pointwise-minimized/{guarded,tight}-domain.br` retain ordinary
count-witness certificates. Fresh processes check both. Their parent hashes,
unchanged declarations, reads, witness instances, and unchanged conclusion
are checked by `extract-pointwise.ts`; only hypotheses may be removed.

## Exact scope

Writing `b = key$4#` and `w` for the ordinary count witness, five premises
remain, at original indices **1, 13, 16, 17, 19**:

1. `size <= 64` (64 is this frozen packet's packing width).
2. `b < size`.
3. `CT[i] < CfgT[b]` for the tight variant; the other uses
   `CT[i] + 1 < CfgT[b]`.
4. The instantiated `canVote` flag body for membership in `S` at `w`.
5. The instantiated `all$2` flag body: membership in `S` at `w` implies
   `Config[64*i+w] = 1`.

The exact bodies are in the certificates. The conclusion stays
`inS[0] <= inX$canVote$3[64*i+b]`, using the saved declarations. Its negation
is original index **20**, retained unchanged. The `all$1` body, `i < size`,
second-key bounds/distinctness, and auxiliary flag-value bounds are unnecessary
for this conditional certificate. Do not infer that its retained flag
premises hold in every branch, or hard-code these names or packing width into
production. The implementation must still derive/instantiate its premises.
Reuse must also validate actual count declarations and term substitutions;
copying witness/read names alone is not proof transport.

## Checks and cost

- Every accepted removal has a newly grown and kernel-checked proof.
- Both final certificates are independently checked in fresh processes.
- Removing the scalar guard still returns numeric SAT for both reduced
  obligations. These are not certified finite-state counterexamples.
- Separate fresh checks find the original guarded numeric premises SAT with
  the conclusion omitted. Removing premises preserves that satisfiability.
- **572.91 / 572.77 counted units** cover the entire greedy reduction,
  including unsuccessful removals and its negative control. They are not
  single-proof cost or an original-harness performance comparison.
- The original unminimized pointwise attempts cost **39.79 / 39.78 units**.
  No fair full-versus-reduced timing claim is made.

This is greedy reduction, not a claim of a globally minimum premise set.
V1 failed before proof because boat omits `runs/` from source snapshots;
V2 mounts the committed certificate directory explicitly. No proof budget
was raised, no kernel changed, and no failed receipt was replaced silently.

## Reproduce on boat

Use `research/mldr-incl/minimize-pointwise-jobs.json` with
`--data runs/mldr-incl-pointwise-certificates-v2:certificate-input`.
The job uses a unique output file and runs `verify-pointwise.ts` in a fresh
process before deleting it. Extract retained artifacts with
`extract-pointwise.ts RUN_ROOT OUTPUT_DIR` (hash/file processing only).
`pointwise-context-jobs.json` uses the same data mount for consistency controls.

The original harness remains UNKNOWN in the pinned A/A+E trials. Only
Lane D's exact-source final gate can authorize a merge; this lemma cannot.
