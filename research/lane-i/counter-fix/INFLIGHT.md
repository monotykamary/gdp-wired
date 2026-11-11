# Continuation checklist (2026-11-11)

Do not change runtime while these exact-source batches run. Branch
claude/mldr-integ. Runtime source78ffca6e, final exact receipt pin
00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7. Only research error-message
coercions differ; `git diff 78ffca6e 00b58ee5 -- core kernel lean-kernel` empty.
D informed, calibration still HELD until acceptance audit, then send pin.

Active final-source tasks:
- full gate 21152f78-093b-4294-9a87-7714e6bfb597 ->
  runs/lane-i/counter-receipt-check
- 28 strict +28 flags-off b56f860a-2a76-4506-9719-94e1bb410c00 ->
  runs/lane-i/counter-receipt-census
- 5 candidate probes c74db480-d21a-45a3-8a03-1af9ac856751 ->
  runs/lane-i/counter-receipt-probes
Input /tmp/lane-i-counter-receipt. Capture includes flags-off-model.ts,
flags-off-measure.ts, 49-law fixtureSHA49a80595..., original modelblob0541fa94...

Also still collect the previous-source diagnostic tasks (do NOT restart):
- 62fa55d0-7156-4c7d-b45f-9042e027b17f -> counter-v2-census
- ccda83fa-5b79-48b5-89c5-9aebac863ddc -> counter-v2-probes
Use ONLY baseline-*.log from counter-v2-probes for final paired E1/E2.
Their source efd70276 is unchanged. Candidate rows there are diagnostic78ff.
Previous v2 full gate230c78aa... terminal:25 tests pass; typecheck failed only
Error|undefined string concatenation in research/probe-run.ts, fixed00b58.

After final batches:
1 Read per-job summary/logs, not just SC exit0. Re-run only genuine failures.
2 Copy final-census logs + old strict/off logs from
   runs/lane-i/hard-cap-final-efd7 into /tmp audit input. Run audit.ts via SC:
   audit.ts FINAL OLD OLD 00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7.
   Checks26keys/conservation/14positiveweights/clockzero/cap15M+1024/all10
   checked verdicts retained/flags-off exactold20projection+new6allzero.
3 Assemble final candidate probe logs plus prior baseline logs into audit dir;
   run probe-audit.ts DIR PIN via SC. It checks original DROP/BROKEN logged
   witness PREFIXES (original Fable logging truncates long states), sets,
   counters/conservation,units/wall. Do not claim full witness-byte comparison.
   Emit receipts and placement.json to report qualified same-large --timing.
4 Commitlint using research/lane-i/common-counted/commitlint.jobs.json with
   --data /tmp/lane-i-counter-messages:message-input. Refresh messages with
   git rev-list efd70276..HEAD first. Include eventual final commit title file.
5 Stage minimal runtime.patch/tests.patch (already in counter-fix; target78ff
   is runtime-identical00b58), D-HANDOFF/RESULT, new runs/REPORT.md prefix.
   Archive successful + failed logs and source IDs. No force/history rewrite.
6 Send exact00b58 pin and schema to ic3-lean for174 calibration+29 confirmation.
   No merge/main/push. .reflex-saved/ must remain untouched.

SCHEMA.md is authoritative:14extras,26raws; tinyNodes/tinyTerms/4reach buckets;
no refunds; actual closure ops vs static fastStep charge separated. New work
pre-admitted, closed generated tiny block uses finite admitted tick credit,
falls back per tick near W. Scoped refusal sticky for same endpoint, inherited
entry cannot reset it, smaller child does not poison larger parent. Root
finally restores. New charges do not cross W; old1024 provisional slack is
NOT automatic for fittedweights. D must confirm slack under final fit.

All earlier b64 tasks stopped/reaped, exact IDs in STATUS old text; do not
resume them. Old b64 census had missing off-model filename; corrected to
flags-off-model. Runtime changes since hardcap efd are solely counter/scope
and newprecharge functions in untrusted kernel/prove header.134 protected
identities and restofprover checkedexact. User hardcap original acceptance
already committed e8d48b20, max15,000,430/10proofs18unknown. Do not release
efd or b64 or78 as calibration pin; onlyfinal00 afteracceptance.
