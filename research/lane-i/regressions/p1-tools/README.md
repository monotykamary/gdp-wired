# Frozen measurement tools

These `.source` files are byte-for-byte copies of Lane B's measurement
helpers (plus the small Paxos checker-only replay). They are data fixtures,
not modules at this directory depth. The input builder materializes them
as `.ts` under a disposable source tree's `research/lane-i-fastloop/`, where
their original two-level imports resolve correctly.

Their hashes are recorded in `runs/lane-i/p1/input-manifest.json`. Do not
silently replace them with a later Track M working copy. The p1 helper
uses the original generated family, pass order `count-first`, 6000 units
and 7000 ms; it reports separately checked conditional certificates, not
an accepted joint family. No extra helpers or optional recovery modes are
introduced by this diagnostic.
