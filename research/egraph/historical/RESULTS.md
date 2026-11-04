# Historical e-graph comparison — bounded results, final gate pending

## Decision

**Partial correctness success, NOT end-to-end acceptance.** The exact historical
TIP theorem now has a checked full proof with a genuine reverse/append lemma use.
The preserved Q3 model is blocked by a checked clause instance. **Neither actual
Paxos milestone-2 open obligation flips.** Native producer/full-gate admission is
still blocked independently; no production integration, merge, performance gain,
Lean replay, or broader-corpus success is claimed.

The accepted implementation remains at `662a1c07e4a521b04a2f05bfc4275d9660eb8ca0`
on its original branch. This isolated additive component changes only
`research/egraph/**`. `BASELINES.md`, `PROTOCOL.md`, `receipts.json` and the committed
fixture/proof manifests bind the sources, exact inputs, settings and raw receipts.
The final component commit is supplied in the handoff, rather than making a
self-referential commit hash inside this file.

## 1. Reproduced real Paxos baseline

Canonical M2 engine/fixture: `444ece6ebe42d202150bc583c0c55b626b4e32c9`, tree
`517d8462ade04456254dc6db0e6132cc4bae94ce`. A separate immutable Git export was
loaded on boat, without altering historical worktrees. Each of the six published
Paxos clauses was prioritized in its own invocation with the **entire six-law
context**, `search:false`, and the historical 25,000 ms cooperative outer ceiling.
The original observer event was serialized once; replay did not rematerialize the
machine through a getter.

| Actual obligation | Reproduced baseline | Complete start/step replay |
|---|---|---|
| one value decided | open at step | no step certificate |
| P1 proposals unique | checked | both passed |
| P2 vote proposed | checked | both passed |
| P3 decision has quorum | open at step | no step certificate |
| P4 one_b left | checked | both passed |
| P5 choosable | checked | both passed |

All eight positive certificates passed `checkMC` plus the historical source-witness
freshness check. These are conditional per-clause results, not proof of the entire
conjunction. Incidental failures of other clauses late in a focus invocation are
not substituted for those clauses' own prioritized result.

Full failed goal identities:

- Safety, 202 hypotheses:
  `58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca`.
- P3, 76 hypotheses:
  `a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357`.

The original matcher failed closed on `if` on both **enabled and disabled** paths.
The source inventory found 202/104 ITE occurrences respectively, with equality,
conjunction and inequality guards. The new optional `IteEGraph` adapter indexes
ITE guard/then/else structurally, meters conversion, refuses reserved-name
collisions and unsupported guards, and decodes candidates before proof use.
It does not drop hypotheses, reduce away either branch, or add kernel rules.

At the **same 100,000 matching units / 512 nodes / 1-second cooperative matching
ceiling**, both whole contexts now exhaust matching fuel. Original and adapted
runs use the exact saved full goals. No enlarged cap, selected easy subgoal,
claimed new clause instance, or counted-proof bridge is substituted for completion.
**M2 remains NO FLIP.** Further whole-context work would need a more economical
index and a checked counted-certificate integration, not a larger budget.

## 2. Actual preserved Q3 model, separately labeled

Instance **`paxos-P5-19`**, wrapper SHA-256
`98bbf35993c89be329a58b31beb8f256cc68f14837007da1fd77792095a7363b`;
payload `2611d4f829c184580f72cee9508d24c9622492b589ae17df058d8a24f4f793df`.
Its original 82-hypothesis ground goal has SHA-256
`0ff5ab54f683403c9b30b27a53a8f096478711a6b26f349f102aa0c0c39480eb`.
The saved model satisfies all its dumped rows under the existing evaluator.

The benchmark adapter reads the historical clause's own affine coefficients
4096/64/1 and decodes the actual explicit `Vote[1:4544]=1` cell to `(1,7,0)`.
Reification equality is independently kernel-checked. E-matching that exact
model-indexed read yields one clause instance in 377 matching units. This small
index is explicitly a saved-model diagnostic, **not** the full M2 index above.

For proof, all 82 original hypotheses remain, together with the saved model's
actual points `size=3`, `Vote[4544]=1`, `Proposal[448]=0`, and an instance of the
original P2 clause. This is a contradiction of that model under the existing
inductive context, not an unconditional protocol proof.

| Case | Outcome |
|---|---|
| disabled | unproved (`sat`) |
| enabled, instance `(1,7,0)` | kernel checked |
| wrong ballot 8 | unproved (`sat`) |
| delete instance from successful certificate | rejected at its goal |

Proof `q3-proofs/q3-enabled.json`, SHA-256
`f18b2065323a34f63577bb69895b03117ebb44bb0067c6882870f7c2a18d868e`,
was also rechecked in a **fresh Bun process**, one complete cyclic node.
Historical Q3 already blocked this model with its own MBQI work. This result
establishes compatibility of the e-graph route, not a new historical gain.

## 3. Exact historical TIP theorem, with real lemma use

Instance **`prod/lemma_09.smt2`**, 612 bytes, SHA-256
`225ccffbf1a98c7334f6be2d86e13efe07ce707e1fcaa8b3b5dd6b4869654888`:

```
rev(x ++ (y ++ [z])) = z :: rev(x ++ y)
```

The input was recovered from the manifest-verified RL archive member
`runs/laneRL/base/research/frontier2/tasks/tip/prod/lemma_09.smt2`.
Translation uses abstract sorts, with **no statement changes**. The precise
association and reverse-snoc formulas already present in
`compare/tip/lemmas-sample30.json` are independently re-proved, not assumed.
Each helper uses `lemmas:false, transfer:false, ms:10000`, with a 20-second
cooperative outer ceiling. Their full proof graphs are retained and rechecked
when combined. The client conclusion is the exact translation of the original
full theorem, with no client hypotheses.

Historical context matters: archived `local-laws-depth2` proved these two helper
shapes but left the root unknown. The earlier claim of zero matching was corrected
in RL's own notes as a **BAD REGEX**. We do not claim matching was newly possible.
Exact rerunning of that dirty historical wrapper is not claimed: it injects core
source and private exports, forbidden in this lane, and requested different
resources. Its original source and failure receipt remain preserved.

A fresh ordinary production baseline on the unchanged `9753` datatype engine
(`proveData`, 57,000 counted ms, 60-second cooperative ceiling) also remains
unproved, at the structure-of-x/structure-of-y case 2. The engine/kernel/translator
Git objects relevant here are identical between `9753cce0` and accepted `662a1c07`.
This is not presented as an exact rerun of the old dirty wrapper.

### Identical-engine adapter cases

All cases share the same full goal, prepared helper graphs and 2,000,000 combined
work-unit / 5-second cooperative certificate limits. Matching uses the existing
500,000-unit / 512-node / 2-second cap. The explicit-hint cases use the same
association equality split; deleting a use does not delete a hard branch.

| Case | Full theorem checked | Root reverse-snoc uses |
|---|---:|---:|
| disabled, same explicit hints | no (`sat`) | 0 |
| enabled, **no explicit hints** | **yes** | **1** |
| enabled, explicit association hint | **yes** | **1** |
| association use ablated | no (`sat`) | 0 |
| reverse-snoc use ablated | no (`sat`) | 0 |

Here “disabled” disables admission of the matched uses; candidate generation is
shared and charged equally across the adapter cases. It is a candidate-use
ablation, not a separately timed e-graph-off run. The ordinary production baseline
above does not invoke this adapter. No production-search integration or claim that
matching alone caused the difference follows from these certificate experiments.

Each successful graph has **9 nodes and 2 root lemma uses** (association and
reverse-snoc). Both serialized graphs passed `refuseCyclic` in separate fresh
processes. Replay checks all nodes, all use premises/descent, and both branches
of every split. The root trees have 6 splits without explicit hints and 4 with
hints. Existing proof search supplies its own ordinary splits; no new automatic
e-graph explanation extractor is implemented or claimed.

Successful proof SHA-256:

- No explicit hints:
  `d6f0f654e62f7b9c19d17f0d1ab60dacf2b07063b72c64482ba84d7c2b367398`.
- Explicit hints:
  `492b6821cea7dde59fd9837858a36789955358021aefac50b38cc73cc9d92773`.

Deleting either root use, corrupting the reverse-snoc proof, or making the
client rank nondecreasing is rejected. The genuine archived broken variant
(SHA `b338202f614781dddadef69664bc876cadfd5c6b423ae0be6e3e6b9b0f623e6a`)
is refuted at `x=[0], y=[1], z=0`; the standard TIP runner separately confirmed
translation agreement on 200 goals and 200 calls, with no skipped samples.
This is one tested historical instance, not a measured corpus-wide lemma-use rate.

## Validation and preservation

- Full e-graph regression suite: **15 passed, 0 failed, 53 assertions**.
- Four new ITE tests include guard/branch-preserving roundtrip, reserved-prefix
  refusal, fuel exhaustion, unsupported guards, and an unchanged-kernel positive
  plus changed-else negative.
- Both `tsc -p research/egraph` and `tsc -p research/egraph/historical` passed.
- Scoped type-aware lint: **0 warnings, 0 errors** (19 files in the final run).
- Exact prepared commit message passed commitlint 19.8.1 with the recorded rules.
- No whole-project gate or new Lean result is claimed.

Every worker requested **2 CPU / 4096 MiB / 600 seconds**; all ran on boat.
Placements identify nonexclusive large VMs, allocated 2 vCPUs on 8-vCPU hosts.
These are untimed correctness receipts, **not timing/speedup or hard memory
measurements**. Cooperative caps can overshoot; actual CPU/RAM enforcement is
not established. See `receipts.json` for each placement and worker exit.

Retained failures include the first overbroad archive index/root-NEXT miss,
a truncated HTTP archive body correctly rejected by SHA-256 in v2, the canceled
pre-dispatch M2 launcher caused by an unrelated tool regex error, and the final
check's pre-dispatch FileNotFoundError when a private redirect file was moved
while the uploader still indexed it. That last failure is infrastructure/input
freeze failure, **not a test result**. The subsequent run used a stabilized file
inventory and passed. None of the original failures or old checkpoint claims was
rewritten. No large archive was restored locally. The owned store server was
explicitly deleted after extraction; all owned controllers are terminal.

## Native evidence chain: explicitly incomplete

Sol reports frozen gate component `8a3b2e42` and diagnostic component `5f6d7baa`.
Its nested native worker path has a successful diagnostic receipt, but production
pre-reduction attempt history, exact one-CPU grant-backed placement, and H01
allocation/exclusivity authority remain unresolved. No eligible native invocation
has been supplied for this comparison. These results have **not** been admitted
through a validated native/full-gate chain. Final end-to-end acceptance is pending
that path and coordinator review of this frozen component. No merge/push occurred.
