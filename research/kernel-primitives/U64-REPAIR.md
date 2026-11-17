# u64 quotient identity: checked repair

## Minimal supported-width regression

`core/fixed-division-proof.test.ts` builds one unsigned64 rule, two word inputs
`n,d`, two word state fields `q,rem`, and a single step assigning `n div d`
and `n rem d`. The law is `d != 0 => WRAP(q*d + rem) == n`.
No reader, source admission, search, or assumed user fact is involved.

The rejected proof was a certificate problem, not a native counterexample.
The captured diagnostic is retained at
`/tmp/kp2-diagnostic-results/u64-first-rejected-leaf.files/rejection.json`:
`identity @step law`, path depth23,163 rows,97 certificate steps. Step86 combines
row84 with row35, multiplier281474976710656 (=65536^3), hitting coefficient
-65536 on `worddiv$64$c$7[...]`. The exact integer product is
-18446744073709551616 (=-2^64), outside the safe-integer boundary. The diagnostic
Number string renders it as `-18446744073709552000`; that rendering is not a
native arithmetic mismatch or evidence that the actual product was inexact.
The unchanged checker correctly returns `unsafe-product`.

Four radix65536 columns are the smallest supported limb count that requires
this global coefficient: three columns reach2^48, four reach2^64.

## Repair without weakening the checker

1. The guarded helper theorem now supplies `c_n = 0`, not merely `c_(2n)=0`.
   This is valid because `Q*B+R=A < radix^n`. Guards still require every raw
   digit below the radix and a nonzero divisor. All four widths have independent
   Lean proofs against the actual normalized helper.
2. `kernel/word-division-cuts.ts` is **untrusted search**. It introduces
   `c_i = multiplicationCarry_i + additionCarry_i` one column at a time.
   Each equality is an ordinary split in both directions. Both unequal
   branches must be refuted by the existing checker; trees are widened back
   to the original goal and the complete tree is checked again.
3. `core/check.ts` and its safe-integer guard are unchanged. Local searches
   share the outer deadline/node budget. No new assumed equality is accepted.

Native `20261117-184058-fxe0fs` first passed the complete identity regression.
Final native `20261117-185742-ovwts2` passed it again, including interpreter and
compileJs boundary runs (0,1,max-1,max with divisors1,2,3,max), and rejected a
shifted false identity. The false law is not labelled BROKEN without replay;
its regression requires that neither public nor kernel PROVEN is returned.

## Legacy proof cost

Only receipts are parsed by `budget-summary.ts`. Each pair runs the existing
Rust u8 Budget fixture in separate fresh Bun processes, swaps exactly four
files against origin/main6119535b7, discards one cold sample, and measures20
warm samples per property and phase. All timed results require kernelProven;
reader/source translation remains unchecked, so public admission stays false.

Original admission `20261117-182645-k3p3b2` completed four exclusive9950X VMs
(80 warm samples/property/phase); its client session closed before collection,
so results were recovered by immutable batch fetch, never rerun. This old
non-strict admission has no local custody journal; recover-close explicitly
refused. All four retained rows are exit0. Do not describe its missing strict
close receipt as verified cleanup.

The repair removes irrelevant whole-goal scans via an untrusted search hint,
and a **negative-only** word-free WeakSet memo. Positive consequences are
always rebuilt from current syntax. Mutation can cause optional consequences
to be omitted, never add stale trusted assumptions.

Final admission `20261117-185742-v0344f`:three independent exclusive9950X VMs,
2/16 pinned vCPUs,0 co-tenants,20 warm samples/property/phase/VM (60 each).
Median paired percentage changes across the three VMs:

| existing property | median paired change | per-VM range |
|---|---:|---:|
|spent <= limit|-8.37%|-16.69% to+14.92%|
|wrapping lap|-3.01%|-24.93% to+26.36%|
|failed spend rollback|-3.67%|-15.79% to+10.74%|

The earlier3-sample regression is not reproduced consistently after removing
these scans. VM/phase variance is substantial; this is not a claim that every
machine/sample improved. Full per-pair medians remain in receipt logs.

Independent Terra rounds8 and9 APPROVE the actual kernel/prover changes only,
including the guarded carry rule, local-cut replay, negative memo and shared
budget. They do not certify generic full-machine Lean export or a release.
