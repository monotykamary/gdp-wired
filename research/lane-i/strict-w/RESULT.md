# Strict-W reader table admission — PASS within measured scope

Final source tree340557e57aa51ca91678dd46a3cbed1017c07c3f, on I committed
d4d600d8dce6b8c49c3ce4023470c83dd1cd3226. Four untrusted runtime files plus
one test; no scheduler draft or protected edit. See SCOPE.md for the argument.
The independent28-pair audit passed; source commit is supplied with the handoff.

## Endpoint results: actual unrounded work, W225000000

| Computation profile | Actual used | Strict <=W | Candidate boundary | Public verdict |
|---|---:|---|---:|---|
| nine historical entries |224999999.10099998|yes|49|UNKNOWN|
| +F three entries (F12) |224999999.62510002|yes|49|UNKNOWN|
| +GDP_COUNT_DEFER_CHECKS (F13) |224999999.62510002|yes|49|UNKNOWN|

All return one explicitly unchecked Inv* proposal. No family closure or new
admission claim. Clean endpoints run on71832531; final340557e5 repeatsF12.
The runtime differs between these trees only by a comment clarification;
tests gained stronger low-price-bucket interleaving coverage.

Both historical51ee and committedI d4 reproduced225000050.62510002 with
all26 raw columns identical. F12 now executes exactly51 fewer table cells
(175168197 ->175168146); every other raw column is unchanged. The old rounded
225000051 is not rounded down, clipped, refunded or granted extra allowance.

The computation profiles are named9/12/13 as before. Supercomputer.toml also
sets the passive diagnostic GDP_CYCLIC_LOG=1 in all these jobs; the receipts
expose it explicitly. core/cyclic.ts's cycLog only prints JSON to stderr.
No GDP_COUNT_C2_LEMMAS, A scheduling or closing-reserve flag was added.

## Gates

- Final340557e5: full scope controls25tests/217assertions; types/lint clean;
  commitlint passed; clean F12 endpoint passed;181protected blobs unchanged.
- Legacy scope controls passed on71832531; default-off remains the old path.
- Native replay on032d92c2:19laws/38goals, four mutation refusals. The artifact
  ise02ef503… and remains research-native evidence, not Lean clearance.
- All28 feature-off legacy pairs finished successfully at15M legacy units,
  baseline5e52d5ee vs71832531. Independent audit:28/28 exact normalized pairs;
  27proven and1unknown (sharded_kv), unchanged.
  This is not a28-original full-work W campaign.

## Isolated amortization check

Batch20261111-101115-vrsqql, one process/VM, alternating mirrored order,
source340557e5. results/benchmark/placement.json: large, AMD EPYC4585PX,
4/8vCPUs pinned, exclusive with0co-tenants. This is not a9950X calibration.

Each loop:1M table units; all other raw buckets unchanged; active clock
tripwire did not fire. Two observations per mode (descriptive, no CI):

- unscoped baseline:3.184573 /3.814908ms;
- scoped amortized:12.471937 /15.544071ms,3970admissions each;
- per-node admission:23.241011 /17.077527ms,1000000admissions each.

No claimed unit saving from the guard itself, and no end-to-end speed claim.
The51-unit endpoint reduction is work refused before execution, not repricing.

## Failed attempts retained

The initiald903ae40 pilot's endpoint passed, but its tests imported fullWork
from wall.ts instead of prove.ts. The next032d92c2 static gate caught a fixture
object's unused label property. Both were test-only corrections; all failed
receipts are retained. The final source tests also ensure low-price buckets
consume >=512 units so they really invalidate a cached block.

A's authorized57a8f1a9 diagnostic stays unchanged and contains no strict-W fix;
its separate direct-admit fallback-deadline hold does not authorize merging it.
D's source/calibration/Lean holds, root, tier split and all prices are unchanged.
