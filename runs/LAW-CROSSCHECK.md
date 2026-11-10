# Law cross-check release hardening

## For the coordinator

Branch `claude/law-crosscheck` starts at the requested `5bbf4bf7`. The fuzzer is preserved separately at `007c0fa5` on `claude/translation-fuzz`; its two queued batches and controllers have been stopped. No version bump, push, release or external contact has been performed.

Work follows the handoff order:
1. Native source-law validation at proof finalization — the core passed 13 focused regressions, check/typecheck/lint and commitlint on Boat (focus v4); first core commit landing. Follow-up temporal/composite entrypoint refusal is in progress.
2. Explicit unchecked API/CLI verdicts, exit 2, docs and breaking CHANGELOG — next.
3. Five historical controls without their specific fixes, and cross-check mutants — pending.
4. Restore the bounded fuzzer, canonical shard/treadmill integration, and a wide default-config sweep — pending.
5. Full gate, private replay, census and quick bar — pending; Lane D review before coordinator merge/release.

The native interpreter uses real JS values (including undefined, NaN, strings, truthiness and object identity), not symbolic law arithmetic or choice indices. Native argument bindings are captured at source entry after destructuring/defaults. Explicitly finite standalone domains are independently obtained from the original TypeScript types and visited in full. A finite domain above the exhaustive bound is refused as unchecked, never relabeled sampled. Unbounded domains retain the original replay seeds and samples; sampling is not a universal semantic proof.

At most one local control process is active. All substantial validation runs on Boat; no subagent has been started. Focused validation history: initial job `20261110-083337-knlj1k` never passed its starting phase and was withdrawn. Focus v2 found an invalid test fixture; v3 found a redundant-undefined-default lint error; both receipts are retained. Focus v4 (`20261110-085807-vsqfs0`) passed all 13 tests (40 assertions), check/typecheck/lint, and commitlint. These are interactive focused checks, not the required submission-class release gate. The current unstaged follow-up wraps temporal/decision finalizers; it is not part of v4.
