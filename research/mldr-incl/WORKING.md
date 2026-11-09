# Lane E — production member premises

## Current checkpoint

Production commit **2047d2be**, on claude/mldr-incl. It adds ordinary bounded
member witnesses and real source-law/flag instantiation. No assertions, fixed
protocol names/widths, kernel edits, or proof-budget changes. The source is
still on the 30c4c889 A/B/F integration base plus the prior audit withdrawal.

Latest captured 34-law family has no supplied p1. Frozen conditional safety
(no support, helpers assumed first):
- baseline UNKNOWN at 6001.055494 units;
- fixed v2 2700: UNKNOWN;
- fixed v2 6000: both START and STEP checkMC true at 3817.24253 units,
  whole-probe 9.625 s wall. NOT original-harness success.

V1 returned a rejected certificate: arithmetic tree checked, but three count
read coordinates depended on their own member witnesses. Existing kernel
rejected it. V2 uses independentCountInstances at all ordinary/cached MBQI
boundaries when member witnesses are active. Preserve the failed evidence.
The new fixture is consistent (non-strict field law, indicator count), with
missing-guard and freshness controls.

## Active task — do not duplicate

8efd60c7-747c-4dfd-a1de-831744254f75, runs/mldr-incl-production-premises-check-v3:
- type/lint and 53 focused tests after fixing missing Counted.j and tuple type;
- isolated early-completion ordering experiment at 6000 (not production).
Class interactive, pinned large. Collect terminal result. V2 already had all
53 tests / 195 assertions passing but its type-check failed on those two fixes.

## Immediate continuation

1. Import **actual lane mappings**: A claude/mldr-gen fdabeba4; B
   claude/track-mldr (was 803129c4, now 6d69e094 research follow-up); F
   claude/mldr-leaves (was 36210941, now 682c8dc6 and initial range integration
   bb61cb8d). The separate Fable wall branch is not Lane F. Read fresh refs.
   Preserve both sides of counts.ts edits. Lane I integrates all lanes later.
2. Run type/lint + targeted tests on merged source. Generate latest family
   afresh, then conditional STEP at 2700/6000. The runner now saves
   production-proof.json including machine, laws, exact instances and certs;
   inspect-production.ts reconstructs both obligations in a fresh process.
3. Run original unchanged harness x3 on pinned large, no preload/env changes:
   bun research/protocols/ic3syn/run.ts --only mldr --ms 60000 --skip broken.
   Keep the 75 s outer watchdog and report actual strict-60 s outcomes.
4. Check used member CInsts and original source premises, not just proposal
   logs. If still above 2700, study existing checked conditional-cut support;
   do not add assumptions. Current 2047d2be changes are sufficient for the
   checked 6000 conditional proof but NOT the whole protocol.
5. Commit small follow-ups and compact evidence. Never edit another worktree;
   research/claude-import/ stays untouched.

## Evidence and acceptance boundary

runs/REPORT.md has the newest conditional result and historical audit warning.
Captured checked archive:
runs/mldr-incl-production-checked-input/archive.br,
SHA256 bc13d4b9c0124e23412a6093affe48bb91062102c44ae675cecd6f72910a0327.
Latest family archive hash:
5c0621847c3b166736d6bbf8bddd6dc6677d743aaa7b91402cccd9fdd467aa78.
Old five-premise conditional files: runs/mldr-incl-pointwise-minimized/.

Lane D final-audit-P80 was read in full. Old 84/87 vs 83/87 and 1073/18
numbers are iteration observations ONLY: roster/unique identity/source binding
and six shard receipts were missing. Withdrawn in 3f3a523c. Do not create more
lane-local gate tooling. Acceptance belongs to Lane D's authoritative gate.
No original 29/29, GATE GREEN, main merge or push is claimed.
