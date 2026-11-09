# Censored deadline-free diagnostic

Exact engine: `5974b9165d6860f1157f3bed3cd66a7e1514e904` on exclusive large VM `bx_25xas5gt` (8 pinned vCPUs). Batch `20261109-052450-ke1brk` was stopped on the coordinator's instruction; the local observer was stopped by exact task id, then `/close` named only this batch. See `../section12-unlimited-v1/cancelled.json`.

The Inv* worker had already hit its external one-hour watchdog: exit **137**, **3,602.85 process seconds**. It remained in initial op 3. The last live observation at 1,425.56 seconds showed **6,562,328 kB RSS**, roughly 6.3 GiB. This is **censored**, not a failed unlimited-work leaf, not a refutation, and not a complete-law result.

Its initial op 0, 1 and 2 spans completed in 243.6923392, 207.9897124 and 131.2118724 counted units (sum **582.8939240**). No end-of-query/shard receipt recorded the ongoing op 3 counter. **The total counted units are unavailable**; the completed spans are only a lower bound. No terminal numeric model or violated set was captured for the still-running query. The queued/successor unsharded Inv2973 work was cancelled, not reported as a verdict.

The archive contains the preserved action journal, probe log and source integrity receipts. `receipts.br` is SHA-256 `8dd98ea98104c48fab42ee21f4d06eab0e4a80bea4b7d095f0446276d2697c13`. It was fetched from the existing VM and checksum-verified; no experiment was restarted to recover it.

Replaced by finite per-op shards and immediate result publication under `../shard-ops-v1/`.
