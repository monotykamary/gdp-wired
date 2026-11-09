# Original-34 range and scheduling input

`family.json` is an exact byte copy of
`lane-b-original-owned-v1/receipts/original-2/raw/family.json`, captured from the
original harness after its finite pass. It is not a hand-trimmed frozen-35
family. Model, caller/support identities and all 34 laws are retained.

- Family SHA-256: `737c233d0efc2f750df5253aa9269f1ddd1db44bf2dbbed9d523b7d6952e22dc`
- `control.tar` SHA-256: `59a91c61968421b22c791f781dbb8344a149e2e70cc95a513d777b01a91312b8`
- Archived `core/counts.ts` SHA-256: `42b55a2c54e18b6059fcc8650869288475c185e49a6933d09b9b54564e02d6a9`

The control is `git archive 5c2d3b70 core/counts.ts`. The balanced range runner
switches only that file between the retained control and the landed range
integration. The independent early-focus experiment restores this pre-range
file before every run; its optional 15.4/15.5 patches are applied only in the
disposable Linux job.

Every measurement uses count-first ordering, 6,000 counted units and 7,000 ms.
An unknown outcome or an overrun is never rounded into a pass. All successful
per-helper certificates require replay against this exact model and roster;
none establish the full family or the original harness's scheduling success.

Run job files through `supercomputer` using this directory as `replays`.
Large receipt expansion/projection belongs on boat, not the laptop.
