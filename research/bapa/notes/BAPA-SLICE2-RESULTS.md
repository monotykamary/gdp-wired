# BAPA slice 2 — one tuple-keyed, uncapped lock-server port

Slice 1 remains the separate commit `fa1748be9`. This slice changes research files and documentation only; it does not alter the canonical registry or core/kernel source.

## Exact credit and limitations

**Existing native tuple keys remove the cap for a port that never reads a sort whole.** The new `research/bapa/lock-server-sized.ts` replaces `client * 64 + server` with `Link : Client × Server` and replaces fixed input bounds with immutable symbolic `clients` / `servers` and `sizedSort.has` domain guards. This is not evidence for slice 1's bounded-quantifier evaluator. It needs no new rigid relation rule.

The checked proof below has the helper **given, not found**: `Link(c,s) => not Semaphore(s)`. It is a kernel-level demonstration, not a new canonical 'nothing written' success.

## Verified statements (helper given, not found)

Batch **20261114-052455-5c21xu**, fetched to `runs/bapa-slice2-03-fetch/`:

- The original guarded uniqueness law holds for arbitrary natural client/server sizes.
- The stronger unguarded law `Link(c1,s) ∧ Link(c2,s) => c1 = c2` also holds over all naturals. Its helper is unguarded too.
- Both ordinary proofs are independently accepted by `checkLaws`; both exported machine theorems compile in Lean. The printed axiom set is only `propext`, `Classical.choice`, `Quot.sound`.
- No positive-size premise: zero clients, zero servers, and both zero are included. No request satisfies the input assumption in those cases.
- Five tests / 187 assertions pass. The original 64-bound radix port and the new port agree on all 9 states and 8 requests per state under a 2×2 request restriction. Interpreter/compiled-JS behavior agrees at 130 clients / 201 servers. The missing-semaphore mutant concretely double-acquires, and reuse of the good proof on it is rejected.
- Whole-repository typecheck and type-aware lint of `research/bapa/*.ts` pass.

The runtime checks are finite correspondence evidence, not the argument for arbitrary sizes; the symbolic checked proofs supply that argument. Runtime native tuple keys retain the repository's safe-number requirement, not an artificial 64 limit.

## No-given-helper searches

Only the original guarded safety law is supplied to `proveRule`, with no hand-written helper and no counted model machinery. The initial 5000ms diagnostic was too small to support a broad failure claim. At Main's request, independent **60,000ms** and **600,000ms** search options were run in parallel in batch **20261114-052608-x6j97p** (`runs/bapa-nogiven-long-01-fetch/`).

Neither completed search found a proof/helper. **Both returned early**, not at their allowed limits: total call elapsed 14,835.84ms and 14,673.56ms; reported search elapsed 13,332ms and 13,210ms. Thus this records two unsuccessful completed searches with larger caps, not 60 or 600 seconds of exhaustive search and not a proof that no helper can be synthesized. Their `sat` induction states are not reachable counterexamples.

## Prover issue isolated, not fixed

Fresh alpha-renamed DSL binders can reuse stale fast-memo instances. Ordinary `proveLaws` falls back and produces the checked proofs above. The one-map minimal repro and the unchanged old `lock_server` kind-law repro are in `research/bapa/notes/BAPA-MEMO-REPRO.md`. No core fix or disabled production check is bundled with this port.

## Retained batches

- `20261114-052200-oed4e5`: initial guarded proof / Lean and runtime tests pass.
- `20261114-052303-2iu2aw`: deliberate stronger-family exposure of stale fast memo, 4 pass / 1 fail; typecheck/lint pass. Not relabeled as success.
- `20261114-052455-5c21xu`: ordinary fallback, both theorem families, 5 pass / 187 assertions, Lean and typecheck/lint pass.
- `20261114-052325-53s24n`: conventional commit message validated.
- `20261114-052707-n1094e`: final gate after the new minimal repro and parameterized search script; 5 pass / 187 assertions, both Lean theorem families, whole-repository typecheck and 5-file type-aware lint pass.
- `20261114-052513-ve0yi6`: fresh/default, fresh/no-alpha, same/default controlled memo comparison.
- `20261114-052608-ia5z0o`: minimal scalar Boolean-map reproduction.
- `20261114-052625-0dqgc2`: unchanged old lock-server kind-law reproduction.
- `20261114-052608-x6j97p`: independent 60s / 600s no-given-helper search caps.

The final gate above was fetched and inspected before committing. Canonical29 is separately pending a final frozen candidate, static review, fresh sealed input, and exact authority (`research/bapa/notes/BAPA-CANONICAL29-PREP.md`); nothing here reuses the consumed canonical packet.
