# Lane I — staged I2 observations

Cumulative candidate: `c9eb0f9c733d122d4b09c7fd7c2ab23e73f0eaf6`, ref `claude/lane-i-i2-coverage`, on b11e1f65.
Its first commit is `17968f8f`; apply both commits or the cumulative
`coverage/candidate.patch`, not only the five-file follow-up. Production has
not been changed. This does not include the separate I1 kernel candidate.

## Implemented and checked

- One raw core-meter object, no weights or budget policy.
- Interpreter expression/condition visits and compiled closure visits.
- Section 18's static expression-node count per compiled step invocation.
- Existing compiled derived-count callback ticks.
- Finite evaluator binding visits, with cached results not reevaluated.
- Actual short-circuit row probes in width-two count-cube enumeration.
- Every candidate tick call, without altering its local 65,536 cap or state.
- Watch tuple observations alongside the original private count.

116 selected tests pass, including ten focused observation tests. Roster,
decoder, type/lint, source/stream audit and commitlint pass. Receipts:
`runs/lane-i/i2-coverage-checks-v2` and `runs/lane-i/i2-coverage-audit`.
No performance, complete-work, protocol-census or integration pass is claimed.

## Integration boundaries

A2 is still separate. Preserve its traceNow import/debug seam and all its
existing test-roster entries when combining. Its full-suite shard failure is
not erased by passing isolated controls. Neither A2 nor the unqualified
generator stack is included here.

I1 is `9f89363c`, pending Lane D's independent 28-certificate audit. Do not
merge that entire branch's generator ancestor; use its documented kernel-only
patch when admitted. Do not use kernel observations for budgeting before D1.

## Remaining I2/I3 work

AST production/substitution and reification; the general infer cube meter;
finite-prefix ticks on the admitted generator; direct recurrence helpers;
manual model-instance evaluation paths; a unified full-work aggregation and
phase ledger. Review dynamic compiled-loop coverage against F1/F3. D2 owns
new weights and W; no placeholder values are treated as calibrated.

The first evaluation fixture failures and the follow-up setup-only failure
are preserved in the state files. All work ran on boat, with no subagents
or new local whole-tree copies.
