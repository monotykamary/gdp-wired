# Verified request-allocation observations — not integrated

- Source: `94b65671b0f81ccfd5e7be71686fc81f35387c94`
- Branch: `claude/lane-i-complete-requests`
- Tree: `1fe9fc742ebe0c4fa25fcf60916f37c54e7ccc37`
- Parent: `41d39043a75e279dc9600e6a33c8107014b67025`
- Parent tree: `1938f7d70a7ed5fb0369a0e76e2e0c2b5a113131`
- Full composition SHA-256: `2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2`
- Three-file delta SHA-256: `5c0b609e3b703d01e05f240d2a8dc82147b7950f520cad264dd408966403519a` (9,047 bytes)

The delta changes only `core/infer.ts`, `core/request-materialization.test.ts`
and `scripts/test-shards.ts`. The observation counts copied fields and the
new assignment at the existing Cartesian request allocation. It does not
change caps, ordering, truncation, RNG calls or checker acceptance.

`20261110-214513-kscywo` passes 164 selected tests, checker erasure, roster,
decoder and type/lint. Three 267-test zero/double/random suites passed on the
same production blobs in `20261110-213747-rlztdu`. Their only source difference
is the unused exact fixture, repaired first for TypeScript parsing and then
for the no-implied-eval lint rule. All first failures remain retained.

Independent audit `20261110-214802-hwwfgg` checks every source and trace hash,
all required checks, and that exact one-file exception. Its export reverses
only the three intended changes, requires the exact parent tree, restores
them, and reproduces the exported tree. A separate Git index replays the
9,047-byte delta on the real parent and confirms the same tree before the new
branch is created. No constructor generator was rerun.

The original model blob remains `0541fa9436e307a6fb716aa5064637b30b893b79`.
The integration working tree is unchanged in `core/` and `kernel/`.
This is not a new cross-CPU census, complete coverage, Bun F3, calibrated
weights, W, or GATE GREEN. The first request-source Node follow-up is next.
