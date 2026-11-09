# For lane B — p1 scheduling comparison (pending)

The production tree and Lane D's `8214a543` → `d3adf3c9` final gate remain unchanged.
This work is for a subsequent candidate, not a replacement gate.

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

Lane B reports 1152.3382236 → 2046.9378360 p1 units. Those are prior
measurements, not results of the pending reproduction here.

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

All measurements are pending. No new production repair or gate pass is claimed.
