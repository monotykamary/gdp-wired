# Lane E checkpoint

Branch `claude/mldr-incl`. Production is **0ee27c7a**, unchanged by the latest
research follow-up. Main is b788e195. No owned jobs or waiters remain running.
No merge, push, GATE GREEN or complete MLDR proof is claimed.

## Current deliverables

- Production commits f6ec83db, 7dc52140, 0ee27c7a: ordinary guarded inclusion
  admission and bounded selection. No kernel or budget changes.
- Exact-source paired diagnostics: **126 pairs**, IC3Syn **84/87 vs 83/87**,
  DuoAI **10/10 each**, broken **0/29 each**; no lost proof/refutation or false
  proof. Source pins and full roster checked. This is NOT Lane D acceptance.
- Seven full shards: **1073 pass, 18 skip, 0 fail**. Complete shard-7 gzip
  and hash prove 227 pass. The original wrapper's singular/plural parsing
  failure is retained. Type/lint + **38 focused tests** pass; the final
  follow-up reconfirms type/lint, three parser tests and four extractor checks.
- Conditional lemma: both original guarded variants check at **39.79/39.78**
  counted units. Greedy reduction retains **five of twenty premises**, with
  the conclusion, declarations and witness instances unchanged. Fresh kernel
  processes check both reduced certificates. Full reduction costs
  **572.91/572.77 units**, NOT one-proof cost. The positive numeric contexts
  and missing-guard controls are SAT, not certified finite-state models.
- Read `research/mldr-incl/CONDITIONAL-LEMMA.md` for the exact five premises,
  original indices 1/13/16/17/19 and unchanged conclusion at 20. They use the
  canVote and all$2 bodies, not all$1. Never assume these flag bodies globally.
- Certs/index/17 hashes: `runs/mldr-incl-pointwise-minimized/`.
  Parent certs: `runs/mldr-incl-pointwise-certificates-v2/`.
- Reduction v1 failed before proof (runs/ omitted from source snapshot).
  V2 mounted the committed inputs and passed. Final extractor tests reject
  changed conclusions, reordered premises and forged parent hashes even with
  success labels. All failures and exact executed plans remain retained.

## Original-harness boundary

144 frozen full-STEP replays selected the desired full-S inclusion but gave
no checked safety proof. Original A/A+E v2, pinned A=48533517, gave six
UNKNOWNs around 59 s. The partial instrumented capture retains 144 files,
omits 405, has 34 initial laws and 284 model queries; retained stages are
pass 0 and show no prioritized safety stage. No 29/29 claim.

New upstream history, read only: A's 74dd9cc5/52b2382f fixes cancellation and
fact checking, still awaiting Lane D re-audit. B's 1db3dc67 rejects its
combined policy after a conditional safety loss. Do not blindly compose it
or transfer our local diagnostic acceptance. These commits are NOT inputs
to the recorded A/A+E experiments. Lane I owns continuous integration.

## Next boundary

Lane B can use the five-premise conditional obligation while still proving
actual branch assumptions and rechecking declaration/term transport. Lane D
must run its authoritative exact-source final gate before any merge. Until
original MLDR is proved, do not move to AFTER-MLDR or call the task green.
Leave the pre-existing untracked research/claude-import/ directory alone.
