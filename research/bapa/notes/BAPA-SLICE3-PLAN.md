# BAPA slice 3 plan — rigid finite instances and naive consensus

2026-11-14. New commits after `142d1f5ab`. Preserve the slice-1/2 commits and their behavior; no memo fix, canonical-registry edit, count rule, or change to old certificate meaning. **Plan review by Fable comes before implementation.** D reviews any trusted acceptance/Lean bridge change.

## One port, and the exact source

Select SECTION-63 row 17, `naive_consensus`, one of SECTION-64.6's ports narrowed to majorities. Restore the original Ivy model, not a strengthened claim about the TLA+ file.

Pinned source: `aman-goel/ivybench` commit `5db7eccb5c3bc2dd14dfb58eddb859b036d699f5`, `ex/ivy/naive_consensus.ivy`, Git blob `798410c0fd8147cdb80286e2cf36ca316c955c66`. Retrieved on boat in batch `20261114-053004-otsidj`, retained at `runs/bapa-slice3-ivy-source-01-fetch/quorum-ivy-source-index.files/ex__ivy__naive_consensus.ivy`. The corresponding `ex/pyv/naive_consensus.pyv` declares `immutable relation member(node, quorum)` and the same axiom.

The source declarations are `type node`, `type quorum`, `type value`, and `relation member(N:node, Q:quorum)`. The source axiom, verbatim:

```
axiom forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2)
```

The original law, verbatim:

```
invariant decision(V1) & decision(V2) -> V1 = V2
```

Keep all three state relations: `vote(Node, Value)`, `decide(Quorum, Value)`, `decision(Value)`. Do not project away Quorum from `decide`, introduce a `Voted` implementation map, replace quorums with counts, or retain radix packing / a 64 cap. `cast_vote(n,v)` checks every Value for no previous vote at n; `collect_votes(q,v)` checks every Node for `member(n,q) -> vote(n,v)`; `learn_value(q,v)` checks `decide(q,v)`.

Important source qualification: the pinned Endive `naive_consensus.tla` has the corresponding transitions and Safety but **no intersection axiom**. It was fetched separately in batch `20261114-052937-6dwlkx` (SHA256 `63cdc8ecfeafd9e423cf0448afbd33ff7bb00f2e76d222ef026bd215e7f5e64f`). Do not claim the new assumption was in that TLA+ file; the requested axiom is explicitly restored from the original Ivy model above.

## Falsifiable implementation hypothesis

Existing Lean `SMachine` already quantifies over arbitrary maps not listed in `maps0`; `SReach.start` requires its immutable `facts`/`pfacts`, and `factsOk` excludes request/state/written/carried data. Consequently, rigid relations and multiargument functions should lower conservatively to read-only function maps plus bounded universal facts, without a new arithmetic proof rule. The new work is an explicit finite-instance interface, exact axiom/Skolem lowering, and its source-to-lowered Lean bridge. Reject this approach if it cannot preserve the instance for a whole run, establish every fact from the public precondition, or connect the original existential axiom to the lowered witness function.

## Fable review accepted (SECTION-75.6, 16135edad)

The only new trusted mathematical statement is the Skolem/source-axiom bridge in `Rigid.lean`; read-only functions known by facts and ordinary 0/1 range facts already exist. No new kernel concept is authorized. If another trusted rule proves necessary, stop and report it for review.

The finite consumer census must explicitly check **several sized sorts in one machine**, two distinct marked guards (Node and Value), and rigid function reads plus native tuple-coordinate reads under them. This is the slice-1 consumer extension required by this port, not a claim that slice 1 already delivered the combination.

Before the port, a minimal rigid example proves `Quorum inhabited => Node inhabited` from the intersection axiom, with no given helper and no existential in its law. It must exercise source lowering, runtime instance validation, the bridge and Lean export independently.

The state-existential helper is discharged through a proof-only ghost map **`learnedQuorum(value)`**, updated to the deciding quorum when a value is learned. It is not the removed model map `Voted`, is absent from source transitions and observations, and is eliminated by the existing ghost-map theorem. The implication is `decision(v) -> exists q in Quorum, decide(q,v)`; empty-quorum cases must not be strengthened into an unconditional finite existential.

The existing suite row remains the majority/counting port (intersection PROVED there). The new port ASSUMES precisely the original intersection axiom and admits non-majority intersecting families. Keep those premises and all given-helper labels separate; neither result is substituted for the other. Concrete witness search always selects the **smallest node**.

## Lean first: no new TS acceptance until these compile

New `lean-kernel/Rigid.lean` (or similarly isolated module), using existing `Sets`/`Bounded` semantics, proves:

1. **Fixed interpretation and framing.** A run has one immutable interpretation of each rigid symbol. Relation values are Boolean; function results lie in their declared finite output sort whenever inputs lie in their declared argument sorts. No step/request can replace these maps; equal tuples have equal reads. State initialization imposes no artificial zero value on rigid maps.
2. **Finite-choice equivalence, including empty sorts.** For arbitrary finite Node/Quorum membership, `forall q1 q2, exists n, member n q1 and member n q2` iff there exists an auxiliary function `meet(q1,q2)` into Node satisfying that body. Its arguments are all preceding universal binders, not a single request-supplied witness. Prove the actual bounded-Nat lowering as well as the typed `Fin` statement, including freshness, range, and tuple substitution. Outside declared domains no extra range/existence assumption is imposed. With Quorum empty the axiom is vacuous; with Node empty and Quorum inhabited no instance is valid. Do not impose blanket positive-size assumptions.
3. **Source precondition to existing facts.** Every interpretation satisfying the public axiom extends to an interpretation of fresh auxiliary symbols satisfying the lowered universal facts. Conversely, lowered facts imply the public axiom. Any accepted machine theorem is therefore about **every original valid instance**, not only instances supplied with a privileged chosen witness. Auxiliaries are fresh and absent from source transitions and the user law.
4. **Original protocol safety.** State/prove the original Ivy transitions and agreement theorem at arbitrary symbolic Node/Quorum/Value sizes, under precisely the source intersection axiom. The source's three commented manual invariants may be supplied as helpers: unique vote per node; decided quorum members voted; every learned value has some deciding quorum. Label these **helpers given, not found**, prove them inductive, and do not confuse this semantic proof with a yet-unchecked emitted machine certificate.

Then D reviews the Lean bridge and any proposed trusted validation changes. Prefer the existing `smachine_sound` theorem via conservative lowering. No `sorry`, new axiom, assumed soundness bridge, or matrix/count rule.

## Opt-in TypeScript / runtime layer after the Lean gate

Add a small isolated rigid-instance module, with only necessary opt-in wiring to Machine/Rule/export and scope validation. The public model declares sized sorts, immutable relations/functions, and axioms in its instance precondition. Keep the public axiom with its quantifiers; lower it only after validation, using fresh auxiliary symbols and explicit range/domain guards.

An instance is serialized finite tables, not an arbitrary JavaScript callback. Bind and privately copy/freeze its interpretation once before initialization; validate cell kinds, function ranges and axioms by exact finite enumeration. Derive auxiliary witness tables by deterministic witness search. Fail closed on malformed tables, invalid axioms, missing witnesses, name collisions, attempts to write/carry a rigid symbol, or runtime rebinding. No setup phase. Relation lookup uses existing native tuple encoding/congruence, not a new radix convention.

Source proofs range over all satisfying interpretations; concrete tables are only for execution/tests, never substituted for the symbolic proof. Exported Lean must expose the original axiom as the source theorem's premise and discharge the witness-extension bridge. If the existing existential-helper certificate route is insufficient, report that separately; do not silently replace the original law or publish only the easier Skolemized theorem.

## Acceptance tests and negatives

- A valid intersecting family that is **not a majority family**, e.g. Node={0,1,2,3}, two distinct named quorums {0,1} and {0,2}. Symbolic agreement must cover this, not just its concrete size.
- Symbolic Node/Quorum/Value sizes with no 64 cap, plus concrete >64 execution, zero-sort cases and duplicate-extension quorum names (Ivy sorts are names, not necessarily extensional sets).
- Exact small-state/transition comparison against a source-shaped independent interpreter over finite membership tables. Original three state relations remain observable.
- Counterexamples: disjoint quorums can learn two values if the intersection precondition is deliberately omitted; allowing a node to vote twice breaks safety; changing membership between steps breaks the fixed-instance contract. Invalid instances are refused in the normal API.
- Reject Skolem mutants: wrong witness range, omitted membership conjunct, partial universal coverage, missing argument, captured auxiliary, or hidden extra source assumption. TS rejects corresponding malformed input; Lean proves the needed premise and supplies countermodels to weakened statements.
- Run existing finite/tuple/exists/function/Lean regressions without modifying slice-1/2 code paths. Preserve old certificates. Canonical29 remains a separately authorized final frozen-candidate measurement, never the consumed packet.
- Run helper search separately if practical; any proof supplied with the three invariants is always labeled given-helper.

## Review and execution

Fable reviews this plan first. All theorem compilation, tests and source fetching on boat through `SUPERCOMPUTER_CONTROLLER=1 supercomputer`; results under `$SUPERCOMPUTER_OUTPUT_DIR`, retain/fetch every batch ID. Only git, edits, reads and quick commands locally. No push or history rewrite. No edits in other worktrees. Report results/blockers only as dated `bapa` lines in `MAIN-INBOX.md`; review requests to Fable/D use their designated channels, never a Main direct message.
