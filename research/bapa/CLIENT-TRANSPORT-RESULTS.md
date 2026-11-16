# Client/server database: checked no-search certificate transport

## Requested symbolic-size result

**Accepted:** all 54 obligations (27 initialization, 27 preservation), including
law 1 `DbResponseSent$g` and law 26 `DbRequestSent$g`. The complete family checker
returns true. Reintroducing the old fixed request bound `r < 64` is rejected.

- Retained capsule: `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0`.
- Retained `Proofs.lean` SHA-256:
  `8d629dfe6d70661809e378ab21ec738a5173613cf1796473f3032942b1f7dbce`.
- Batch: `20261115-230417-t7bk42`; native exit 0, 39.45 s job time.
- Artifacts: `runs/bapa-transport/client-sized-v1/client-server-db-ae-bound-substitution.files/`.
- Receipt: `checks.tsv`, `Checks.lean`, `Checks.log`, `REPLAY-METADATA.json`.
- `ClientServerDbAeSizedChecks.lean` preserves the checked `Checks.lean` source.
- New proof searches: **zero**. Original successful modules were reused by SHA.

`CertificateBoundSubstitution.lean` is the general candidate transformation.
`ClientServerDbAeSizedTransport.lean` applies it to this retained family:

1. Insert fresh fixed parameter variable 1000000 as table column 0.
2. Rewrite each source `<64` guard as `<size`; keep the witness bound rather
   than erase it. Both ghosts store sort elements: request `r` and node `n`.
3. Shift all old column references, including cells, tuples, monomials, splits,
   leaf rows, square rows, cuts, equal-cell pairs and source hints.
4. Replace the recognized strict/weak bounds and their complements by symbolic
   size rows (`63` becomes `size-1` in the strict upper-bound interpretation).
5. Preserve every original tree branch and arithmetic proof step. No pruning,
   Boolean cleanup, new invariant, or arithmetic proof search is used here.
6. Run the complete existing kernel on the result. Then use Lean `decide +kernel`
   to prove the observed 54-vector, complete family result and negative control.

Theorems `obligations`, `family`, `surviving_bound_refused` use `[propext]`.
The reachable-family `laws` theorem and generic `checked_transport` theorem use
`[propext, Classical.choice, Quot.sound]`, and no other axioms.

The negative control appends an old literal `r<=63` row at shifted column 3 to
an original leaf without adding a hypothesis. The kernel rejects that candidate;
the refusal is separately proved in Lean. A successful family check alone is
not substituted for this control.

## Earlier erasure baseline and independent cleanup

The unmodified bound-erasure candidate checked **52/54**: preservation of laws 1
and 26 failed, and complete family acceptance was false. This is a checked
refusal, not a lift. Artifacts:
`runs/bapa-transport/no-packed-client-v3/client-server-db-ae-harness-fix.files/`.

The independent cleanup candidate then checked **54/54** and complete family
acceptance, with the same old-bound mutant rejected. Batch
`20261115-230228-ybko59`, native exit 0, 44.57 s job time; artifacts:
`runs/bapa-transport/client-cleanup-v2/client-target-boolean-cleanup.files/`.
`CertificateBooleanCleanup.lean` changes only a rejected leaf where the target
kernel's existing `leafRows` contains a positive constant. It uses that available
row and one `.input 0` step; no new premise, SAT/SMT, or arithmetic search.
The symbolic-size result above does **not** depend on this cleanup.

## Exact proof boundary

These are theorems about the explicit translated Lean machines, not yet about
the original source implementation. The following source bridges remain pending:

- Parameter/admission correspondence with the symbolic-size source.
- Typed map and public-law correspondence.
- Ghost/witness projection and initial-state correspondence.

Production/source acceptance remains **PENDING**. This client already uses tuple
keys, so this result is not a proof of the still-in-progress packed-key translator.

## Reproduction

Use `research/bapa/client-sized-transport.jobs.json` with the retained capsule's
`lean/` directory mounted as `transport-client`, and the verified baseline
artifacts mounted as `transport-prior-client_server_db_ae`. Run through
`supercomputer` with `--backend boat --strict-once --max-attempts 1` and collect
that one admission. The script checks reused module source hashes, records all
Lean exits and refuses acceptance if the old-bound negative control passes.
