# R4 timed-arm read-only diagnosis

Source: exact `9eb09b8326fc2670fad6725f774ab1b252c4d343`. No new job, replay, solver call, or source mutation was used. These are deductions from retained output and pinned control flow, not a reconstructed proof trace.

## Where and why

The worker/driver exited 0; the public verdict is UNKNOWN, `proven:false, checked:false`, with `recipe closing replay declined; recipe pass: target-held`.

`core/counts.ts:792-801` builds the needed family from held rows and calls `replayScopedCountProof(m, family, row.payload, Infinity, {deferToClosing:true})`. One such call returned undefined; line 801 immediately returned the diagnostic. This closing call did NOT reach `finish(...)` or the unchanged whole-family `checkCountedLaws` (lines 675-707). It is a replay/identity/validation-preparation refusal, not a public counterexample or completed certificate.

`core/count-recipe-controller.ts:103-105` sets `target-held` only when every requested target belongs to the greatest premise-closed held family. The original target is `one primary per term`. All 17 members below were held proposals in the submitted needed closure. Held does NOT mean every proof was checked: unchecked full-context proposals are explicitly supported. Additional held members outside the needed 17 are not enumerated by this output.

The exact failing member, obligation and return case were NOT recorded. Earlier members may have replayed; later ones were not attempted after the first decline. That boundary cannot be identified. No individual member can honestly be marked as the failing one or as publicly proved/checked. The final whole-family check was not attempted for this closing call.

| # | Member | End status established by receipts | Per-member counted units |
|---|---|---|---|
| 1 | every C0 cell is a value of its kind | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 2 | every Copied cell is a value of its kind | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 3 | every Config cell is a value of its kind | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 4 | one primary per term | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 5 | St at most 1 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 6 | fields: St[a]=1 -> CT[a]=CfgT[a] | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 7 | fields: St[a]=1 -> CT[a]<=CfgT[a] | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 8 | fields: St[a]=1 -> CfgT[a]=CfgT[b] -> CV[b]<=CV[a] | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 9 | every x with x < size: never Copied[x] is 0 and 1 <= started | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 10 | every x with x < size: never 1 <= Copied[x] and picked is 0 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 11 | every x with x < size: never 1 <= St[x] and started is 0 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 12 | every x with x < size: never 1 <= CfgT[x] and started is 0 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 13 | inX: no quorum canVote/3 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 14 | inX: stored guard reconfigs/inS or disabled/0 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 15 | fields: Copied[a]=1 and started=0 -> Config row is C0 | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 16 | fields: CV[a]=CV[b] and CfgT[a]=CfgT[b] and Copied[a]=Copied[b]=1 -> Config rows agree | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |
| 17 | count cubes: every x with x < {"op":"var","name":"size"}: never Copied[x] is 0 and 1 <= inX$row[x] | Held proposal; public UNKNOWN; individual check state not exported | Unavailable |

## Seven refusal categories

Pinned `core/count-proof-scope.ts:110-147` can decline on: (1) duplicate family names; (2) scope identity (missing/changed owner or premise, or its later checked machine-identity guard); (3) obligation count mismatch; (4) missing certificate or failed `mcGoal`; (5) exact no-search `replayCountCertificate` failure; (6) `checkMC` false on a non-deferred proof; (7) deadline. The 17 retained names are distinct, excluding (1) for this submitted family. Cases (2)-(6) and member/obligation cannot be discriminated without the scoped payloads or events. The later machine-identity guard must not be omitted from future instrumentation.

Hypothesis, NOT a finding: case (5), for an unchecked full-context proposal moved into the smaller needed family. Context-generated pair/marker rows can depend on cells supplied by laws not cited as facts. No retained timed proof tree or failing row confirms that mechanism; do not guess the member as Inv*.

## Budget or structural?

This observed closing refusal is structural, not a reported allowance refusal. Search ended `target-held`, not `phase-cap`. With the target in the held closure, closing takes the `legacy` callback rather than the subset `reserve` refusal route (`core/count-closed-family.ts:38-46`). Replay is passed Infinity. Under FULL, `withDeadline(Infinity)` adds no endpoint; `wallAt()` is a counted end, not wall time (`kernel/prove.ts:260-264,355-365`). Meter exhaustion throws through the enclosing path rather than producing this clean structured reason. There is no error, reserved work is zero, only the root endpoint remains before unwind, and the ledger settles clean. The root consumed ~6.12G of 288G, leaving ~281.88G.

Increasing the root alone does not repair a missing/invalid replay relationship for these held payloads and this family. This is NOT a theorem that no other certificate, allocation schedule, or accepted larger family could close.

## Accounting and its limits

Total counted units are exactly `1763976685204992144111239005 / 288230376151711744 = 6120023533.801700...` (`measurement-total.json`). The root ceiling is `288000000000`, not consumed work. Leading raw deltas are tableCells=4850484039 and ticks=1042592206. Driver wall=5740.76946675s; native wall=5746.63s, observations only. No rho/W/calibration/reference-second claim.

Per-helper construction, checking, rescoping and replay costs, and safety-only counted units, are UNAVAILABLE from the timed arm. `driver.ts` installs counts/ledger observers ONLY for instrumented mode. This receipt has `observerInstalled:false, trace:null`, one aggregate counter delta and weighted rational, but no law/phase partition. Assigning those aggregate counters to particular helpers or safety would fabricate attribution. The instrumented arm may supply recorded attribution; this report neither waits for nor assumes it.

## Evidence

Directory: `/home/user/VCS/working-remote/open-source/gdp-wired-trackM-closure-9eb/runs/r4-cap64-20261112-081430/mldr-3g-timed.files/`.

- `TIMED-TERMINAL.json` (same control directory): SHA256 `3f684d3475a242be80c02dc9c2da6fa465a85191948bc4d02a91800023dde902`.
- `verdict.json`: `0394d86d90bea705a61e899da350941e4368cad31bae5e696964340f055fd369`.
- `measurement-total.json`: `9bba4d219bfd4fdc345b41104a82d5c3c2756e19fa8a9458d5c6be7d28b1189b`.
- All 41 exported files were hash-verified against `ARTIFACTS.sha256`: `d0b7d72b7e1924208daa6cda242d01f2350f30657bad0ea8408e9c33474876ea`.
- The inspected counts/controller sources were diff-verified unchanged from exact 9eb.
