# Retained BAPA Lean export

The symbolic-size retained-export gate passed. The third attempt was admitted
as `20261115-171832-0p798m` before the sandbox restart, then recovered by one
read-only fetch after credentials were restored. It was **not resubmitted**.
Its native worker exited 0; strict admission close remains unverified (the
one read-only close-recovery attempt reported cleanup incomplete). This is
one export fixture, not a 29-family proof or a solved source projection.

`proof-emit.ts` is a fresh-process data consumer. It accepts a saved closure plus
its independently retained SHA-256, restores the exact term ordinals/memo IDs,
rechecks the supplied certificates, and writes a Lean 4.34.0 project. It never
calls the general `toLean` route or a proof search. Example inside a bounded
supercomputer job:

```sh
bun research/bapa/proof-emit.ts \
  --capture "$CAPTURE/closure" --sha256 "$CAPTURE_SHA256" \
  --out "$SUPERCOMPUTER_OUTPUT_DIR/project"
cd "$SUPERCOMPUTER_OUTPUT_DIR/project"
lake build
```

Use the outer `SUPERCOMPUTER_CONTROLLER=1 SUPERCOMPUTER_NO_BUILD=1` convention.
The emitted status is `EMITTED_NOT_CHECKED`; a separate Lean build and axiom gate
must succeed. The family theorem is about the **captured producer machine**.
The source-projection qualification is preserved, not promoted. A symbolic size
parameter in that machine stays symbolic, but this is not automatically a
TLA+/Ivy correspondence theorem or an all-29 result.

## Fresh-process boundary

`retainedSMachineToLean` and `retainedCMachineToLean` check their supplied proof,
force kernel reduction (`decide +kernel`), and reject unsupported function,
history, sum and unresolved existential routes. The usual path seeds only the
exact family; a missing family is a refusal, never a search fallback. The usual
proof cache and exporter mode are restored on return or throw.

Native certificate checking may extend process-global term interning. It is
**not rolled back**. Capsule replay is single-use and requires a pristine term
registry. A failed replay can leave a prefix interned: discard the process,
never retry or renumber the same capsule there. The CLI enforces this by running
one fresh process per export. Direct callers must honor the same boundary.

Current CLI supports a unique usual family or one counted family. Witness or
mixed-producer assembly is refused with the original capsule untouched. Lean
identifiers are restricted before interpolation. No `sorry`, `axiom` or
`native_decide` is admitted in generated proof source.

## Split-check boundary

Monolithic emission is not the MLDR recipe. Its 32-GB path must keep one common
full-family declaration, split each actual INIT/STEP certificate at a checked
frontier, prove auxiliary side conditions, join each tree, then join every
original family entry and derive the original family theorem. A subset-family
induction is not equivalent. The historical 35-part MLDR partition is evidence
about that old artifact, not a justified fixed partition of new sized proofs.

The reviewed port is now in `proof-parts.ts`, `proof-frontier.ts`, and
`FamilyParts.lean`; see `PROOF-PARTS.md` and shared commit `dfcaa6010`. Five tiny
Lean projects passed the full INIT/STEP family and axiom gates. This is an
exporter library, not yet a capsule-consuming split CLI.

## Alpha-only source bridge

Use `--projection alpha` to request a checked correspondence candidate for a
plain or inferred unique retained family with checked local binder transport.
The source machine and public laws are rendered
from the capsule's original input, in the same injective name basis as the
producer. Proposed quantified-flag renamings are **not trusted**: Lean checks
`QAlpha.validAll`, equality of the renamed source and producer, and each public
law and key list. `QAlpha` then transports reachability and the complete retained
family theorem to the original source. The resulting `_source_lawN_holds`
theorems are the public claims, not merely the producer's `_laws` theorem.

```sh
bun research/bapa/proof-emit.ts --capture "$CAPTURE" --sha256 "$SHA" \
  --out "$SUPERCOMPUTER_OUTPUT_DIR/source" --projection alpha
# Build the complete project, then run scripts/lean-gate/gate.ts on its build log
# and BapaProof.lean. Every source theorem is included in #print axioms.
```

The output still says `EMITTED_NOT_CHECKED` until the separate Lean gate. Default
emission/receipt fields are unchanged. Alpha mode rejects counted and witness
routes, empty public families, and unrepresented `stated`, `some`, `ex`, `finite`
or `witness` law metadata. More complex renaming patterns may be refused; there
is no fallback to a JavaScript equivalence claim.

Independent pi Terra review found two gaps (unsupported law shapes and a
changed default receipt field); both are closed. Native batch
`20261115-194427-jerb74` passed types, 9 tests / 33 assertions, retained consensus
source proof and axiom gate, changed-body rejection, variable-capture rejection,
manifest/protocol-tamper refusal, and commitlint. The source input is capsule
`ed33f406d61ac50918cff1d69c81cbf843eebf417eb05091544a082f80def1fe`;
`bapa_consensus_source_law0_holds` uses only the three allowed axioms.
`_alpha_valid` and `_alpha_result` are axiom-free. This is a checked source-port
projection for this symbolic-size consensus input, not a TLA+ translation proof
or an all-29 claim. No proof search was repeated.

Earlier alpha attempts remain recorded: `20261115-193440-46vp7u` failed a control
AST typecheck; `20261115-193843-iyc8no` proved the source theorem and rejected the
bad body, then stopped on an incorrect log matcher. Neither is a full gate pass.
## Inferred families and local binders

The same `--projection alpha` mode also accepts `route=inferred` only when the
captured source machine is structurally identical, or has proposed quantified
and row binder changes that Lean validates, and every public law is an
unchanged member of the unique retained family. The **entire** inferred family
and its proof are checked and emitted; helper laws are not assumed without
being discharged by that family theorem. Counted and witness routes remain
separate.

Independent pi Terra review and batch `20261115-195418-q7plzy` passed: types,
7 tests / 18 assertions, both retained `lockserv` and `lockserv_automaton` source
projects, all source-theorem axiom gates, and commitlint. Both source laws select
entry 4 from the complete family and use only the allowed axioms. No search was
repeated. See `inferred-projection.jobs.json` for the exact capsule hashes.

The later combined `QAlpha`/`RowAlpha` gate covers `twophase`,
`two_phase_commit`, `learning_switch` and `learning_switch_i4`. It checks
whole-machine equality after both local transformations and retains every
helper. The counted exporter uses the same row transport. See
`INFERRED-ALPHA.md` for the exact source, regression and isolated-control gates.
## Witness source families

`--projection witness` preserves the complete retained family and projects the
original public existential laws through checked scalar/map ghost witnesses.
A separate `BoundGhost` theorem handles source binders sharing names with
ghost variables; free ghosts remain excluded. Three source cases are checked:
`simple`, `simple_regular`, `client_server_ae`. See `WITNESS-SOURCE.md` for
exact receipts, supported contexts and the two isolated exporter corrections.
No new protocol search was run.

## Current evidence

- `20261115-171208-vix4lb`: typecheck succeeded; a counted fixture used an invalid
  binder colliding with the symbolic parameter. Fixed the fixture, not the check.
- `20261115-171352-xms2pe`: typecheck and four retained-export tests (22
  assertions) passed. The new symbolic native fixture did not retain a proof
  under its diagnostic 1M budget; no Lean stage ran. The revised fixture uses
  the shared generous budget and persists its native result even on failure.
- `20261115-171832-0p798m`: native exit 0 in 77.26 s; typecheck, four tests /
  22 assertions, one no-given symbolic-size native capture, fresh-process
  retained emission, Lean 4.34 build and axiom audit, commitlint. The theorem
  `bapa_symbolic_choice_laws` uses only propext, Classical.choice and Quot.sound.
  Capture SHA `11afc14f45950af60d149448daf7c984ecc240aa5c85df3122accb5af2c807bb`.
  Recovered row SHA `652eccc5e0198a639733a2b7c85f5667378fa7baabe3927c98c95580a87b3ae5`.
  Original-source projection remains unqualified, as reported by the capsule.
  Artifacts: `runs/bapa-proof-emit-03-recovered/retained-export-gate.files/`.
- First and second attempts were each fetched once after recovery and their
  closed admissions verified. The successful third worker is terminal, but
  its interrupted client's admission close needs separate completion; no
  cleanup success is claimed.

`proof-emit.jobs.json` is the focused gate: one new no-given symbolic
fixture capture, fresh-process emission, Lean build, and the repository axiom
auditor. The emitter core change was independently reviewed by pi Terra
`e6f205e8125e470991e7e8d6a4089f4c`; identifier validation and the explicit
single-use term-replay boundary address the findings. There are no trusted
Lean/kernel-source changes in this slice.
