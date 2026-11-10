# For lane B — p1 regression reproduced; refinement pending

Lane D's frozen `8214a543` → `d3adf3c9` final gate remains unchanged.
An uncommitted conservative scheduling draft is under separate qualification
for a subsequent candidate, not a replacement gate.

## Exact inputs

- Validated control: `97463c564351448373ca49f6af980b31b1a0f0c5`,
  `core/counts.ts` SHA-256 `fdfee67b293d9899545413df765768a8b388d56985e98facb838cacac62be91c`.
- Current repair: `d3adf3c9589ec014a158b6f42ecfb091c999bb43`,
  `core/counts.ts` SHA-256 `2cfb115fe42bcf4e1824c6f95323689a114058bcbd85e4a7e3559fde26ac487a`.
  Both hashes exactly match Lane B's retained before/repair receipts.
- Original generated p1 family: SHA-256
  `5dbdbf766e9949b051d0764920f1bcc3707690cd6852fca6d0bcf18674fbdac4`.
- Frozen 45-law Paxos family: SHA-256
  `1a956aa3c04217a3f426837e88558de8888faeb0e3fc7dfc5e0270edd68550bc`.

Lane B reports 1152.3382236 → 2046.9378360 p1 units. Those prior
measurements are now reproduced exactly by all three new paired repetitions.

## Falsifiable hypothesis

The p1 request has one quantified key and reads the unary `inX$row` count.
The regressed Paxos request has two keys and reads a packed binary count.
Try early bounded completion only for single-key requests whose requested
count maps are unary; preserve sparse-first scheduling for everything else.
A disposable worker patch tests this without modifying production.

This is an arity-based scheduling hypothesis, **not** a claim that every
helper expansion is linear: the p1 family also contains binary and four-key
count-reading premises. Existing completion limits, work/wall allowances,
source-premise checks and native proof acceptance remain unchanged.

## Admission and acceptance

`runs/lane-i/p1/probe/admission.json` binds task, snapshot and batch;
`runs/lane-i/p1/input-manifest.json` binds all 170 input files.
One exclusive worker runs three rotated repetitions of exact control,
exact repair and disposable unary-priority policy. Each p1 attempt retains
its original 6000-unit / 7000-ms diagnostic allowance and gets a separate
checker-only replay against the unchanged generated family. Successful
frozen Paxos certificates get a separate INIT/STEP replay. The two current
policies additionally get one unchanged strict 60-second whole-Paxos run.

Required before choosing a production fix: reproduce p1's regression,
recover its validated cost, and preserve repaired Paxos work/results.
These remain conditional per-target proofs and one-run screening, not a
joint accepted helper family, five-repeat protocol qualification or a final
gate. The first-countermodel alternative already reviewed by Lane B is not
substituted: it adds 41.3331660 p1 units and lost `learning_switch_i4` in its
own census.

## Initial result: regression confirmed, first prototype not accepted

Batch `20261110-062712-4vl6nq` completed on one exclusive AMD EPYC 9455
worker. All three repetitions give exactly:

| Source | p1 units | Frozen Paxos solver / full work |
| --- | ---: | --- |
| Validated control | 1152.3382236 | unknown, 4,719,042 / 224,064.6210 |
| `d3adf3c9` | 2046.9378360 | checked, 38,917 / 26,285.6192 |
| Unary-priority prototype | 1152.3382236 | checked, 38,917 / 26,285.6192 |

All nine p1 certificates and six successful frozen Paxos certificates pass
separate native replay. These remain conditional per-target certificates.
However, the single whole-Paxos pair is **not work-neutral**: full work
1,037,946 → 1,038,476 (+530), solver work 6,915,544 → 6,916,948 (+1404),
both proven. The first prototype therefore does not meet the requested
joint criterion, despite restoring p1's original cost. No speed claim.

A second disposable experiment requires a separate relevant count premise;
it retains per-law whole-run work traces. Task
`3431abef-abdf-4e94-8afa-126c50780bdc`, batch `20261110-063516-cuuvdp`.
The conservative production draft additionally requires an actual quantified
key, so concrete goals keep their original sparse-first behavior. Its type,
lint, refusal tests, p1 replay and exact whole-Paxos work check are pending in
task `bff38ac0-d682-4852-8bf7-572f364ef00c`, batch `20261110-063659-6z5xy4`.
The original work-increase receipt is also being independently audited with
missing/duplicate/source/certificate/archive refusal tests.

## Residual-cost attribution and corrected draft

The second probe again restores p1 but still adds exactly the same whole-run
work. Its per-law trace isolates that increase to the aggregate-only
`members$Qs keeps members's bound 2` goal: solver work 20,007 → 21,411;
full work 27,916.6078 → 28,446.5038. Requiring another count premise alone
is therefore insufficient. The corrected draft also requires ordinary map
reads in the requested clause, so pure aggregate bounds remain sparse.

The first draft validation is retained as failed: its new test reused a
count binder, and staging overwrote its restore configuration with older
`8de9dadb`. The original post-main full-suite packet correctly names
`d3adf3c9`; it was not changed. The corrected helper explicitly verifies
`d3adf3c9`. Its type/lint, scope tests, old p1 cost, exact whole-Paxos work and
commitlint are running in `48d3771f-2b25-4743-afae-a123ba811f0b`.

## Corrected policy: targeted qualification passed

The mixed-clause guard additionally requires an ordinary-map read in the
requested law. It passes exact-`d3adf3c9` source restoration, clean type/lint,
25 tests / 108 assertions, roster validation and commitlint. Independent
p1 replay is checked at **1152.3382236 units**. Whole `paxos_epr` is proven
at exactly **6,915,544 solver / 1,037,946 full work**, matching the repaired
baseline. Qualified count-source SHA-256:
`7a4c830848afa2d05393bdd00c546393092cf1f94d5ce9cdee8a2aad9189abd4`.

Five exact-commit pairs now pass with zero audit issues: every repaired p1
uses 1152.3382236 units, and all ten whole-Paxos runs use exactly 6,915,544
solver / 1,037,946 full work. The worker is one exclusive EPYC 9455.
The final independent evidence/type/lint check failed with four TS2532
indexed-access diagnostics in the timeout evidence auditor; later checks
were not reached. The four accesses are corrected for requalification.
Its separate commitlint job passed. This is not a full-suite or
final-gate pass; the original failed prototypes and failed draft remain
retained. Lane D's existing gate is unchanged.
