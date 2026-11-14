# Fail-closed stale-binder memo reproduction — for D / Fable

No prover or kernel fix is included in slice 2. Main requested a minimal reproduction and a check of old-protocol reachability.

## Minimal case

`research/bapa/repro-stale-binder.ts` is one Boolean map, one input, and an update setting that cell to false. It uses **no sized sort, no native tuple, no quantified transition flag, no helper, no count**, and proves only the map's generated kind law.

1. Make rule A and run `proveSetFast(A.machine, A.kindLaws())`.
2. Make the structurally identical fresh rule B, whose generated binder has a different `key$N` name.
3. Run `proveSetFast(B.machine, B.kindLaws())`.
4. Run ordinary `proveLaws` and independently `checkLaws` on B.

Batch **20261114-052608-ia5z0o**, fetched to `runs/bapa-minimal-repro-01-fetch/`:

| Configuration | A | Fresh B fast | B ordinary, independently rechecked |
|---|---|---|---|
| default alpha memo | proven / checked | not proven / not checked | proven / checked |
| `GDP_MEMO_ALPHA=0` | proven / checked | proven / checked | proven / checked |

The default witness contains old `key$2#` and new `key$4#`, with `Flag[key$4#]=2` unconstrained by the cached old-key instance. This is an untrusted prover false negative, **not an accepted bad certificate**. Its reported `sat` state is not a reachable counterexample to the actual rule.

The earlier tuple-port comparison, batch **20261114-052513-ve0yi6**, also succeeds when the same Rule object is reused (stable binders), and fails only for fresh binders with alpha memo on. All ordinary fallback proofs independently recheck.

## Suspected trigger

`kernel/prove.ts:1939–1967`: `alphaText` canonicalizes fresh names for memo lookup and support comparisons, while the retained `Settled.inst` and proof terms contain the original binder names. A fresh alpha-equivalent Rule can therefore reuse proof state with obsolete free witness names. Final proof construction/check does not silently authorize it. Review must decide whether to rename cached terms consistently or refuse incompatible binder reuse; no such edit is made here.

## Old protocols can reach it

This is not specific to BAPA. The unchanged original `lock_server` reproduces it on **kind laws only**, after two fresh `p.make()` constructions in one process. Batch **20261114-052625-0dqgc2**, `runs/bapa-old-memo-01-fetch/`: default second fast proof fails at `every Link cell is a value of its kind @step`; alpha off succeeds; ordinary fallback rechecks in both cases. This is **not** a canonical safety-law run and does not claim the canonical worker encounters the same construction sequence.

Static reachability: `core/infer.ts:728–740` calls `proveSetFast` for fast candidate-set retries and may normalize a Rule with `withSumsOf`; `research/protocols/ic3syn/run.ts` normally makes each protocol once, then its broken variant. Old `client_server_db_ae`, `learning_switch`, and `learning_switch_i4` also use native relation paths (`models.ts:363`, `:607`, `:624`), but the minimal scalar-map case proves native relations are not required. Thus one cannot dismiss old ports based only on lack of BAPA finite metadata.

## Run only on boat

Use `bapa-minimal-repro.jobs.json` and `bapa-old-memo.jobs.json` through supercomputer. Their JSON outputs deliberately report observations rather than asserting the bug must remain. See `bapa-fast-cache.jobs.json` for the three controlled tuple-port variants. Fix review belongs to D/Fable; no core edit is bundled here.
