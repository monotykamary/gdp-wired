# Hard-cap-only checkpoint — NOT the calibration pin

Tested integration source: efd702761f03c320939679912e6d0f2579696010.
All 28 originals: 10 proved+checked, 18 unknown, all unchanged.
Maximum: 15000430 units against 15M; slack 430 <= stated 1024.
All pre-endpoint query/event prefixes and successful-proof raw vectors are
identical. All 28 flags-off receipts agree except provenance and independently
measured wall telemetry; every raw/phase/event/query and verdict field agrees.
Every strict run has zero forbidden wall reads.

22 tests / 100 assertions; full type/lint clean on 1,776 files; the baseline
fails the new guard. 134 protected file/model identities and the prover body
below its cancellation header remain exact. Every job ran on supercomputer.

See LOOPS.md (13 cases and exact between-poll units), CHECKPOINTS.md (each
new source site), runtime.patch and tests.patch. Both native probe passes were
audited to preserve raw counters and complete baseline verdicts.

Initial two-catch pilot was insufficient. The first full pilot (1a8906a2) met
the numeric cap but was rejected because it promoted local deadlines to whole
search cancellation. The final helper reads only the enclosing work endpoint;
local cuts remain untouched. The first flags-off audit compared wall telemetry
and was corrected to exclude only wallMs/exclusiveWallMs and provenance.

## Added coordinator requirement — pending

D calibration is HELD. This source is NOT released for it. Tiny constraint
search nodes are uncounted; reachability evals need distinct weighted accounting.
User requires counter fix + cap integrated and validated, then one exact
claude/mldr-integ pin for D's 174 calibration cases and 29 confirmations.
See counter work checkpoint in STATUS.md. No main merge or push.
