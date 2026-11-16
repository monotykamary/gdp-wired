# Retained counted-family split checks

`proof-parts.ts` exports `emitCountedParts(id, bundle, options)`. It consumes the
same full retained `FamilyBundle` as the single-file emitter, after the caller
has restored the exact term prelude in a **fresh process**. It invokes the
retained native checker; it does not invoke `proveLaws` or search for a different
certificate. This is an exporter library, not yet a capsule-consuming CLI.

## What is split

- `proof-frontier.ts` constructs a canonical weighted frontier of each actual
  primary certificate tree. It visits real leaves, not an assumed complete
  binary tree. Its independent verifier rejects missing, extra, duplicate,
  prefix-overlapping, below-leaf and noncanonical pieces.
- Every tree piece uses the same machine, declarations, full family, variable
  table, original hypotheses, counted reads/instances/picks, auxiliary cuts,
  and exact split-path assumptions.
- Separate Lean modules check both INIT and STEP for **every** family entry,
  all global and entry conditions, witness/read freshness, counted conditions,
  and all lemma, frame, monotonicity and linear-cut conditions.
- `FamilyParts.lean` joins checked children to the original root check, then
  joins the original `checkMCF`, `cEntryCheckF`, `checkCMachineF`, and
  `cmachineF_sound` path. It never treats a subset of the family as inductive.

The emitted status is always `EMITTED_NOT_CHECKED`. Source emission and native
checking are not a Lean receipt. A final project must compile **every imported
piece and the final assembly**, and pass the existing axiom gate. Only then
can a separate verifier record its scope; no all-size/public-source claim is
made by this module.

## Bounds and refusals

Options are explicit: positive `weightLimit: bigint`, `maxOutputBytes`,
`maxFiles`, `heartbeats`, and `recursionDepth`. Structural weight is a
scheduling proxy, **not** an RSS bound or proof-search budget. An oversized
real leaf or common context is refused. Global and auxiliary-condition checks
are currently indivisible; there is no fallback search, context dropping,
reshard loop, or presumed resource success for MLDR. Use the planned 32 GB
check lane for a separately authorized real MLDR capsule, not this tiny gate.

## Focused gate

`proof-parts.jobs.json` typechecks the generator and tests, then checks five
small generated Lean projects: no auxiliary cuts, frame cuts, monotonicity
cuts, linear cuts, and both monotonicity and linear cuts. The latter variants
have multiple family entries, with controls corrupting both INIT and STEP in
the second entry. No protocol search is run.

```sh
SUPERCOMPUTER_CONTROLLER=1 SUPERCOMPUTER_NO_BUILD=1 supercomputer run \
  --jobs research/bapa/proof-parts.jobs.json --out runs/bapa-proof-parts-N \
  --class interactive --backend boat --strict-once --max-attempts 1
```

Independent pi Terra review found no blocker. Batch
`20261115-191837-8ra7sp` passed the typecheck, 19 tests / 161 assertions,
all five generated Lean 4.34.0 projects and every printed axiom gate, plus
commitlint; native job exit 0 in 145.43 s. The first attempt
`20261115-191429-jutmug` passed types/tests but failed Lake dependency discovery
before proof checking. Only the fixture's complete module-root list was fixed;
the proof bridge, generator and certificates were unchanged.

These are synthetic split-check controls, not new protocol proofs. The source
projection bridge remains a separate acceptance gate.
