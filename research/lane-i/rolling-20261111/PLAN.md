# Rolling D-GREEN component integration

Baseline: `5e52d5ee032bd1f534209f7480b2c7ce2640cdc7`, runtime `bfe647cf`.
Branch remains `claude/mldr-integ`. This follows the quotient evidence handoff;
it does not withdraw or silently rewrite that tested source.

## Falsifiable acceptance contract

Integrate the approved untrusted components, each behind its existing explicit
opt-in flag. With those flags absent, all 28 original legacy receipts must equal
this baseline (results, events, queries, proof/trace digests, raw counters) after
only the established timing/source-label normalization. Targeted native and
negative tests must pass with flags enabled. Every protected checker/Lean blob
must remain byte-identical to `PROTECTED.tree`; no cache or check-once work enters.
Any contrary receipt blocks the integration until explained and repaired.

## Approved sources and receipts

- B `edd8c4b5747b0471508082082d92085bd84aae87` then its child
  `47b338d512833dc3f112a72185210c546c4d02e0`:
  D `research/verify-all/lane-b-queued-gates-20261111/DECISION.md`, backed by
  `lane-b-source-gates-20261111/{REPORT,GATE,SOURCE-AUDIT}` and
  `lane-b-counted-originals-20261111/RESULT.md`. Scoped source/default GREEN;
  no B10 policy or W promotion.
- K3 `c22420222bf4351d7b4922a550ecf0abd23a71e9`:
  D `research/verify-all/k3-deferral-c2242022/{REPORT.md,GATE.json}`.
  Default-off intermediate row-check deferral only; final full-family checking stays.
- A `5dec706542a2c97993589f47f89e0ce5fe208188`:
  D `research/verify-all/lane-a-premise-local-0e5014b4/{DECISION,RESULTS}.md`.
  Scoped production factory convention, 3/4 local reserve plus full fallback;
  inherited later external enclosing-deadline limitation remains.
- F family route at `c87fcb75c2880d51b86820ae98d4a0f261d0ed65`:
  D `research/verify-all/lane-f-clock-free-c87-gate/MAIN-REVIEW.md`: now
  source SCOPED GREEN (35 tests / 140 assertions; old test parent RED/c87 PASS).
  Approved staging prerequisite met. Preserve I checker, use authenticated
  dependency closure and re-gate full family and default-off28 together.
  New lifted-family / threshold-field / load-marker prototypes remain excluded.

## Dependency and composition checks

The B patches are not self-contained on this line: several row/leader/query/
strategy modules in their approved base are absent here. Port only their
required untrusted dependency closure from the exact approved source, not its
whole tree (which predates I's hard cap and the 0.48 safety changes). Preserve
I's counted clocks, counters, cap checkpoints and release validation.

A and B independently added `count-premise-view.ts`; compare and compose their
APIs explicitly. Do not overwrite one feature with the other. Ask the component
owners for minimum closure and test entry points before finalizing each port.

After each component, record provenance and targeted receipts. Give lane A one
exact combined source for its MLDR run. Gate the final composition with all 28
flags-off originals and targeted suites, then stage it for D. No defaults,
weights, W, trusted checker, Lean, K cache, main merge or push changes.
