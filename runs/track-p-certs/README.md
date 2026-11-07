# Retained STEP certificates (zero search)

Requested C14-style packs:

- `c9/goal.json`, `c9/proof.json`: C9 STEP using its own PRE invariant; 12 raw / 17 encoded hypotheses.
- `c11/goal.json`, `c11/proof.json`: C11 STEP under the original family19; 27 raw / 32 encoded hypotheses.

Each goal has `{scope,raw,decls,gg}`. Each proof is a `CountCert` with `{reads,insts,picks,tree}`. `source.json` records the exact unchanged fixture hash, family indices and instantiated original PRE laws. No auxiliary hand-written fact is added.

Authentication is exactly `checkMC(pack.raw.hyps, pack.decls, cert)`; `research/track-p/check-certificates.ts` performs no search, no growth, no goal reconstruction. The exported files were checked on boat: both true; removing a count witness rejects both; solver search work remains 0 with no nonzero search costs. Receipt: `check/zero-search-certificates.log`.

Kernel SHA256: `596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2`.

| Artifact | SHA256 |
|---|---|
| c9/goal.json | 96693f267b1dfa17ce76caf30754d552df7804425c845bdf81aa05d25ba6082d |
| c9/proof.json | 4e95c0afde042e383f494f8d52b4b1c40e505443ed2db9e5e9dabccba8a12eed |
| c11/goal.json | 97612173ae500bd2101a4220bcefadfc8201be22cb5146edb79c4e29f5bcb2fd |
| c11/proof.json | fbcd3bfd428be99ea8ed5307226a55739d873a61ef3186571e74eeb108ad5134 |
