# Historical db14ee14 input provenance

The original-protocol model source is unchanged across A 5aa76818, db14ee14
and current 7eccce26: Git blob `0541fa9436e307a6fb716aa5064637b30b893b79`.
The old full kernel subtree was `52ca0f7464ac5fbaad66e46b85cd0a2f217f7925`,
with prover blob `fff9319a4abe5449ef3282d94840fedbb3f7f736`. It is intentionally
NOT the current exact admitted full kernel subtree.

The historical measurement and driver scripts are frozen in commit aba20fe7,
under `research/lane-i/candidate/`. `measure.ts` has Git blob
`dc1df107fb9d4c734f16ce61f5369a692be83e52`, identical to the actual data pack.
SHA-256 of the actual scripts in the original data pack:

- measure.ts: `720cb69b6ada5846fa905748c9a30a02b82c10a3ef4f3fa6676b16c392721bfa`
- run-model.ts: `64a5d2370e2f376e77af1653db95fe0929eb579b02cad1be3a599002cd5a29db`
- verify.ts: `69a86ed6cc93069464e3976722857650bed0ef67e3eb220d6295a7f23c60e584`

The data pack's original archive hashes are in HISTORICAL-INPUT-SHA256SUMS.
Restore the aba20fe7 scripts to reproduce historical runs; the current strict
verifier deliberately refuses the old candidate's kernel exceptions. Never
weaken the current verifier to make a historical source look admitted.

Raw results were emitted as gzip JSON plus SHA-256 and are retained in
receipts/. The final independent audit matches target/source pins, the full
work/strategy/tier flags, weights, all 20 raw counters and exclusive phase
conservation, weighted totals, verdict consistency and all 28 roster pairs.
The full source/profile audit and six negative controls ran on Boat in
20261111-025225-grpnep. Metadata materialization on the controller does not
execute a solver. None of this constitutes work-meter calibration.
