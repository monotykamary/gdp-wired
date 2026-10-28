# NEXT (gen/protocols3, after the sums-kinds merge)

Standing (Modal, runs/protocols3/m2, 02cec45): nothing written at 60 s: lock_server_sync, lock_server_async,
decentralized_lock, ticket_lock (4 of 10); at 10 s: lock_server_sync (1). Written invariants 8 of 10 (m1). Broken
variants refused as before.

Done this round: proven-first context before the whole set (ticket 44 s -> 27 s locally); the round's env switches
removed; one walk for keys and keys per map.
Measured no-go: halving the first search where a sums pass follows (loses lock_server_async at 60 s); a bigger sums-pass
share (decentralized still unknown at 10 s: its second pass needs more than 10 s in all).

Pending: the full bar against c4dff18 (gen/protocols3), speed against c4dff18 and 3cdf37e.
