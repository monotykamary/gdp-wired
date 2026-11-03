# Security laws — untrusted source-policy layer

`gdp-wired check src/handler.ts --security --no-propose` proposes bounded, deterministic
security candidates over extracted names, including broken candidates. Candidates have
`review: "required"`; none is an authorization specification until a person reviews it.
They never become assumptions for one another and do not affect the CLI exit code.
Copy an intended candidate's `gdp: law` comment into the code to check it as accepted policy.
The normal source checking, kernel, replay and `gdp: env` pipeline is reused.

## Templates

The public `gdp-wired/security` module exports `securityLaws(spec)` and
`securityTemplates(extraction)`. Each returns ordinary law text, not trusted proofs:

| kind | fields | meaning |
| --- | --- | --- |
| authorization | effect, requires | `effect implies requires` |
| workflow | effect, prerequisite | `effect implies old(prerequisite)` |
| quota | used, limit | `used <= limit` |
| ledger | balance | `balance >= 0` |
| isolation | map, identity, fields, optional key | two universal laws, over old AND new rows; every foreign row's presence and fields unchanged |

Each spec also has `name` and optional `method`. Expressions use the code's names. For
scalar maps use `fields: ["value"]`. Include EVERY security-relevant record field.
An empty field list checks presence only, not content. Generated templates use all fields.
A custom quantifier `key` must be fresh (automatic proposals choose one).

```ts
import {securityLaws} from 'gdp-wired/security'
securityLaws({kind: 'authorization', name: 'only admins credit',
  effect: 'balance != old(balance)', requires: 'admin', method: 'credit'})
// -> balance != old(balance) implies admin; paste its gdp: law comment above credit
```

A workflow law's `effect` should describe the event (e.g. `shipped != old(shipped)`),
not a permanent state unless that is intentional. Quotas over maps may be stated directly:
`forall k in accounts: accounts[k].used <= accounts[k].limit`.
Read confidentiality is a **two-run** law, not inferred from absence of writes:
`securityLaws({kind: 'isolation', name: 'private reads', identity: 'tenant', seeing: 'result'})`
produces `isolated by tenant seeing result`. These candidates are also proposed for map handlers with results. See core/laws.ts and core/relational.ts. No promise
that a single handler's invariant rules out unmodelled database operations is made.

## Attacker and environment

Inputs range arbitrarily within the reader's types; requests may repeat and occur in any
order. Role and identity fields supplied by a request are NOT trusted authentication.
Bind a policy to the actual authenticated identity, or explicitly model that boundary.
The policy itself is not inferred from a missing guard. Boolean/choice requirements are
alternatives; even a proven alternative may be the wrong policy. Numeric parameters
also range arbitrarily: a nonnegative limit needs validation in the constructor.

Without `gdp: env` a handler is one atomic step. For concurrent code use the existing
`gdp: env read committed` / `snapshot` / `atomic` models in core/system.ts. Environment
refusals must not fall back to atomic proofs. These are model-relative results; an
interleaving is not labelled a replay on a real database. HC2 owns ORM/handler reading;
no replacement ORM reader is introduced here.

## Owned-mutation confidence benchmark

The [mutation benchmark](mutants/README.md) checks ten complete owned training modules with generic operators
and explicit source policies. Its [result](mutants/RESULTS.md) is 16/16 mutants refuted and replayed on source,
0/10 clean programs refuted (13/13 clean laws proven), and 26/26 versions read. It includes private-read
noninterference and source-level lock/transaction/CAS mutations, with additional native-runtime race checks.
This is a small synthetic confidence corpus, **not** additional upstream CVE recall. The deployment-isolation
case is explicitly model-relative.

The separate [pinned-upstream cohort](mutants-upstream/README.md) measures local mutations of two
MIT-licensed components we did not write: 9/9 mutants detected and source-replayed, with 0/2 clean
policies refuted. Its declared boundary covers every public callable operation, not every property or
whole application. The [result and selection record](mutants-upstream/RESULTS.md) preserve reader
refusals and configuration requirements; this is not a CVE or ecosystem-coverage claim.

## Recall protocol

`cases.json` is a small transparent seed set, NOT a representative security benchmark.
Every published item has an advisory URL, public fix SHA and its parent. Only these
published targets and OWASP Juice Shop are fetched. `recall.ts <id>` checks unmodified,
complete pinned checkouts, records original source bytes and hashes, wall/check time and exact refusals.
Run it via supercomputer; all fetched code and receipts stay under `runs/`.

A detection counts only after an intended law refutes the vulnerable original, its
concrete run is reproduced there, and the fixed original is proven or at least not
refuted. Generated candidates, guessed policies, synthetic equivalents, missing
dependencies, compilation failures and unsupported readers are NEVER counted as finds.
Refusals remain in the in-scope denominator; also report extraction coverage separately.
Do not call an unrefuted fixed version proven. The training source in core/security.test.ts
is deliberately written for this lane and must be reported separately from upstream apps.

Receipt admission also requires exactly one original side per required version, a successful
reader status, and unique entry/constructor/policy identities. Failed or ambiguous receipts,
blank replay evidence and unread stated laws are refused. Constructor overloads are distinct:
a proof for one initializer cannot clear a refutation for another. This is consistency checking
of supplied evidence, not cryptographic attestation of a replay string.

`score.test.ts` includes a paired, **self-owned synthetic** source control: the CLI checks both
complete versions, and the exact counterexample is replayed on each unchanged source before
admission. Generated candidates alone still do not count. These controls do not rerun upstream
vulnerabilities or change either the published/training denominator or the fixed-only cohort's
`strictRecall: null` result.

`score.test.ts` also checks a self-owned Java class with two constructors. The same
CLI witness runs through `javac`/`java` on both versions and both initializers; an
unchanged broken initializer cannot borrow the already-safe initializer's proof.
This toolchain-dependent control skips only when Java is unavailable and is run on boat.

For a policy on an entry with multiple initializers, the fixed counterpart must retain
all original constructor contexts and check that same named expression in every fixed
context, including newly added ones. One repaired overload does not count while another
still refutes the policy or omits it. Unrelated entries are not combined into that family.
`fixed-family.test.ts` adds an owned original/partial/complete Java control and is imported
by the existing score-test shard entry. Unknown fixed verdicts remain unknown, not proven.

The same module checks a fixed source that adds an integer constructor: both original
initializers are repaired, but an unsafe new initializer still blocks admission.
Original witnesses run on all three versions; the added initializer's own witness runs
only where that signature exists, with its exact integer argument preserved.

`policy-identity.test.ts` also compares self-owned source variants with a renamed law,
a weakened law, and the genuine repair. Exact frontend policy names and expressions
must match the original contract; native replay judges that original contract even
when a variant declares a weaker one. These controls use the existing score-test shard.

The same source-control module covers repeated policy names, including identical and
conflicting expressions in both declaration orders. Ambiguous declarations stay unread
rather than selecting a favorable proof; native execution alone does not clear ambiguity.

`constructor-argument.test.ts` adds a separate finite argument-sensitive control: the
original boolean constructor argument actually enables enforcement. Flipping only that
argument changes the native outcome for unchanged calls and source bytes. This does not
upgrade the older unused-argument fixtures into a general forwarding guarantee.

The module also checks two meaningful boolean parameters: swapping their positions
or flipping either alone changes the original's native outcome for the same witness
calls and source bytes. This is a finite parameter-binding contrast, not a generic
argument-order guarantee.

`call-order.test.ts` adds a finite stateful contrast using only allowlisted `arm()`
and `hit()` calls. Reordering the same call multiset changes the original native policy
outcome while source and empty argument bindings stay fixed. This is not a general
multi-call replay guarantee.

Its fixture-only replay gate validates the entire nonempty trace before dispatch,
rejects malformed/unknown calls even after a valid prefix, and supplies one frozen,
order-preserving snapshot. Negative controls require zero dispatches on rejection.

An additional owned Java entry-marker probe arms the launch observation before and
after invalid traces. The finite rejection cases reach neither its real replay-spawn
boundary nor its entry marker; this is not a general process-isolation guarantee.

The owned result-row adapter also requires successful process completion and one
complete, strictly framed row with a matching call count before evidence is recorded.
Fixed harmless Java probes cover absent/malformed/truncated output, nonzero exit and
timeout; acceptance here means fixture-row validation, not a policy proof.

## Measured coverage

The complete-corpus baseline on 2026-11-03 is tree `7db037f` (main `927a521`): **18 published,
fixed advisories plus one upstream Juice Shop target**. Strict CLI recall is **0/18 published and
0/1 training**. All 37 original revisions were fetched and hash-checked against retained evidence;
all baseline extractions refused, with no pipeline errors. Extraction coverage is **0/18**, not a
hidden success or evidence that the programs are secure. The three additions are django-allauth
inactive tokens, Flask-Security OAuth freshness and MLflow trace authorization.

A separate six-case Solidity experiment uses the repository's concrete mocks, or an added
constructor-only subclass/internal-library caller, with the original bodies unchanged. All 12
original hashes verify and all 12 deployment contexts are recorded. The vulnerable Initializable
revision now extracts; the other 11 sides refuse subsequent subset boundaries. Coverage on both
sides remains **0/6** and strict findings **0/6**. This subset experiment is not a full-corpus rerun.
See `solidity-harness-measurement.json` and [the explicit harness scope](../../docs/SOLIDITY.md).

See [RESULTS.md](RESULTS.md) for per-case blockers and `measurement.json` for exact source hashes.
A separate original-code OAuthlib runtime replay succeeds only on the vulnerable revision. It is
**not** a CLI/prover discovery and does not increase recall. `oauth-client-replay.py` retains that probe.
Neither the baseline nor the harness subset has produced a reviewed policy refutation with an original replay and a checked fixed counterpart.

Trust and measurement references: README.md; docs/ARCHITECTURE.md (frontends versus
source); research/ROADMAP.md §5–6; compare/tip/README.md (translation and independent
counterexample checks); research/protocols/engine/DESIGN.md (candidates versus checked
laws); kernel/MUTANTS.md. No trusted kernel file or Lean admission rule changes here.
