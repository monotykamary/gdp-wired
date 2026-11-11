# F conditional integration — scoped native/default gate

Exact tested runtime index tree:
`ba0c639da71d0b15670650fd41b64e75f32f081d`, on committed reader6f05 and B/K3/A.
The code commit adds these sources plus documentation/receipts; no later
primitive, final-STEP or evaluator-admission changes are included.

## Native receipts

Native batch `20261111-080556-34mpgb`, recorded in
`runs/lane-i/rolling-f-default-v2`: **34/34 jobs passed**:

- All28 literal feature-off original pairs versus5e52d5ee.
- Native full-family replay:19 laws/38 INIT/STEP packets, no skipped packets.
- Unchanged `checkCountedLaws` accepts the same19-law closed artifact.
- Four mutation classes reject: empty tree, missing witnesses, missing cuts,
  and witness-freshness collision. Separate packet-valid/global-collision
  control passes (1 test/7 assertions).
- Original-family source/admission audit:49 source laws/19 retained; noncount
  machine, original counts and prepared machine are alpha-equivalent using
  the separately tested declared-binder normalization.
- The exact old clock test SHA2563d8aca2f... passes in its original legacy
  meter mode. Separate complete-work reader controls cover500000 and5M;
  observed/unobserved proof and full raw vectors match with zero raw clock use.
- Types/lint pass on1967 files.

Closed artifact SHA256:
`e02ef503f9dbbaee4abd79780a2061f37de283bdac8451290439e344c9b0c03d`.
This is independently checked supplied evidence, not a claim the online
integrated search discovered the whole family within W.

## Strict feature-off preservation

Separate batch `20261111-081449-8hnlp1` passed exact normalized comparison of
all28 pairs. Normalization drops only source/target/custody and wall telemetry;
raw counters, work, results, proof/query/event data and generated candidate
sets remain exact. Verdicts are27 proved/checked,1 unknown (`sharded_kv`) at
15M **legacy** units. This is not the raw-work-v1 W campaign.

The preceding e7bceb87 run passed34 execution jobs but failed this strict
audit for11 originals. Diagnosis: B's three production supportOrder calls
unconditionally requested count-first scheduling with STRATEGIES off. The
helper's explicit API was intentional and is unchanged. Only those3 callers
now supply a machine when STRATEGIES=1; the strict28-pair retry proves the
feature-off repair. Prior failed receipts remain in runs and the diagnostic.

## Scope and handoff

F roots/helpers remain the C87 conditional route, not the generic producer.
B hoist/frame interfaces and K3 deferral are retained. Reader6f05 is the only
previously authorized protected exception;180 other protected identities and
original reader decoding bytes are checked by the runner. No checker, Lean,
price, budget allocation or new final-STEP deferral is introduced in this stage.

Native logs, strict summary and hashes are in `results/F-default-v2`;
full paired receipts remain at `runs/lane-i/rolling-f-default-v2`.
Final full-work/online/W admission and calibration remain pending.
