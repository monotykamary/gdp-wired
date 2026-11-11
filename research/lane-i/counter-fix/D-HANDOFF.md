# Lane D handoff

**Source pin: 00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7**
Branch claude/mldr-integ. D currently uses it for PLUMBING ONLY. This requests
review; it does not claim D approval or calibrated W. No main merge or push.

Review `runtime.patch`, `tests.patch`, `SCHEMA.md`, `RESULT.md` and `results/`.
The runtime patch is against efd70276 (which includes the earlier hard cap).
Core/kernel/Lean at78ffca6e are byte-identical to00b58ee5. Only untrusted
cancellation-header code changes in kernel/prove.ts; all134 protected
identities and the rest of the prover are checked exact.

raw-work-v1 has26 raw keys and14 strictly positive extra weights. Do not pad
old eight-weight vectors silently. New counts are integer/monotone, reach
buckets exclusive, charges pre-admitted. Closed native blocks have a finite
admitted maximum, no refunds and per-site fallback near the endpoint. Caught
refusals cannot reopen the same endpoint or a nested scope. Definitions and
coefficient-dependent slack are explicit in SCHEMA.md.

Proof gates:25tests/111assertions;1783-file type/lint;28strict+28flagsoff;
12checked/16unknown, all10prior proofs retained; max15,000,385.9024 at15M;
zero strict forbidden-clock reads; all26 columns/phase conservation checked.
Flags-off means exact old20 projection plus6newzeros, not unchanged raw shape.
E2 sums of native node statistics equal raw counts; drops/broken sets and
logged witness prefixes unchanged. All new columns observed across E1/E2 and
census; tiny is not invoked by the28 originals and is not claimed there.

Remaining calibration is your gate:174 fits and29 confirmations only with
approved source/profile and qualified placements. Recheck the endpoint slack
under the fitted vector; the old1024 provisional bound is not universal.
Counter columns may be correlated, not uniquely identifiable.

Guest identities supplied: small bx_ncxu6yrz, Ryzen7 9700X,
boot1d8479f9-f9ab-4e3a-9de3-31e40aa17826; large bx_y4fnjbmr, Ryzen9 9950X,
boot31a9a509-ebc0-4982-bda0-143ec46551b0. os.cpus/proc agree but native CPU
placement fields empty; native binding remains mandatory.

The provisional prices severely mismatch measured wall costs. Per-evaluation
admission adds overhead. See complete raw vectors and timings before fitting;
no claim of speed preservation or calibrated W is made.
