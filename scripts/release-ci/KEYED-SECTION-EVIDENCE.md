# Keyed source-section identity for the 0.50.1 gate

## What is unchanged

The two inherited failures are the final `simpa ... using hl'` statements in
`outbox.law0` and `outbox.law1`. Their terms, error kinds, expected and actual
types are unchanged. The entire 1,524-line section beginning with the unique
`def outbox_machine` and extending through EOF is byte-identical in both
retained files:

```
SHA-256 ddc438097071ddeb85e15be463da45dacf23dd886ac7c7523df520b59acd671a
```

The errors are at one-based section lines **1475** and **1480**, column **11**.
The historical file starts that section at line 4462 (errors 5936/5941); the
ordinary diagnostic capture starts it at 3604 (errors 5078/5083). The raw
absolute positions and complete error bodies remain in
`known-failures-keyed-evidence.json` and in the native diagnostic logs.

## Why those absolute positions differ

All 858 removed lines are in the earlier **`nist_goal6` certificate**, not in the
failing outbox code. The smaller tree has 429 fewer `.split` nodes and 429 fewer
`.leafAt` nodes; those 858 missing serialized nodes account for the line shift.
Other goal trees have the same line and node counts; some fact indices and
`nist_tab6` ordering also differ.

The tentative explanation that the 0.50.1 inference fix found a smaller
certificate was **refuted**, not confirmed, by a paired control. The control
started from `ec6e64c6910318b18551f87f6d2362100750adcc` and changed only the
`core/infer.ts` patch from `71dafbbdf`:

| Paired input | `nist_goal6` lines | Splits | Leaves | Outbox start |
|---|---:|---:|---:|---:|
| Current inference fix | 1481 | 739 | 741 | 4462 |
| Only that fix reverted | 623 | 310 | 312 | 3604 |

The effective inference source hashes were respectively
`a92b7d4de2bec5d34c5c41cf140a8a166a43bf8f9a0e2d7bd11613650577e7e6` and
`7d7ccd38ed460401efa0ff7dd4fb47c0a20c128491001b8f3b6c80630f9493a1`.
The full generated source hashes were respectively
`a8355850016a6f33c90ba9305f9c3db7167aa65068f7754493ebd5979c3ea4dd` and
`bf629190b78f2ea20736a6f173d409d5dedb50b1eead34d8c914af23b92f5d0b`.
They match the earlier historical/diagnostic files in that order.

Both paired runs included inference tracing. The earlier ordinary diagnostic
capture was not independently Git-provisioned and did not retain the effective
inference source hash. Its different certificate therefore must not be sold as
a proved improvement from the release fix. The deeper selection mechanism and
whether timing, environment or source provenance explains that earlier capture
are not established by these receipts. No cache defect or timing cause is claimed.

## Lean verification

Both paired generated NICT+NIST prefixes compiled under the unchanged standard
Lean kernel and axiom gate, exit **0**, with **no errors**. The four printed
NICT/NIST safety and liveness theorem dependencies contain only `propext`,
`Classical.choice`, and `Quot.sound`. Each run reports the same harmless unused
`or_true` simp-argument warning. Both strict-once jobs have validated cleanup.
This checks the preceding section independently of the known failing outbox code.

## Gate identity and limits

The gate uses the captured source, not a worker-supplied hash, to derive:

```
Keyed.lean:section=outbox_machine@<section SHA-256>:<relative line>:<column>
```

The entire diagnostic body follows that key unchanged. A different section hash,
relative position, column, error kind, type, additional error, absent source or
ambiguous section remains a blocker. Errors in NIST or any earlier section are
not normalized away. The absolute lines remain evidence rather than the stable
identity. All other Lean location rules and all 22 inherited failure identities
are unchanged; no exception was added.

The release's full suite reconstructs its exact committed Git tree and verifies
native artifact hashes. Neither an ordinary diagnostic upload nor the paired
counterfactual substitutes for the fresh final-commit 28 replays, 11 gates and
245-job suite.
