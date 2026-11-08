# T-F1 — final check retained

Same exclusive eight-vCPU VM `bx_3kjzmmhv`. Research snapshot only. The sole
behavior change defers `proveCountCases`' pre-transport `checkMC`; the final
harness's original `checkMC` expression and the kernel are unchanged. Every
`checked:true` still requires that final check. Production code is unchanged.

The five-law run (`../section8-f1-v2`) preserves all verdicts: three checked,
two unproved. All three proved laws' counted units are identical. The two open
laws hit the unchanged 60-second wall, and their counted work differs, so this
is not a trace-equivalence or controlled wall-speedup claim for those laws.

A follow-up records each root call on the three proved laws. The three calls
are **one expensive pre-transport step check, one almost-free initial check,
and one expensive final step check**, not three equal-cost step checks.
Deferral leaves the initial and final checks: exactly one per returned obligation.

| Law | Control kernel wall | Deferred kernel wall | Calls, control → deferred | Target |
|---|---:|---:|---:|---:|
| one primary | 4.416 s | 2.601 s | 3 → 2 | <=0.4 s |
| Inv3915 | 8.444 s | 4.292 s | 3 → 2 | <=0.5 s |
| Inv1758 | 27.746 s | 15.674 s | 3 → 2 | <=1.9 s |

In particular, Inv1758's control checkMC calls are 13.430 s / 0.000202 s /
14.305 s. The deferred calls are 0.000296 s / 15.661 s. Thus the proposed
three-to-one cost division is structurally wrong. This pass line is not met.

Absolute costs are much higher than the previous census; the reason is not
established. CPU time tracks wall time in the per-call receipt (e.g. final
Inv1758: 15.661 s wall / 16.020 s process CPU). A separate health probe found
no remaining Bun/Node/TypeScript process other than itself and negligible CPU
pressure, so it does not support a current orphan-process/contention diagnosis.
Do not extrapolate these walls to the prior census or claim a Gate 1 regression.

Both successful snapshots pass TypeScript and type-aware lint. The first
150-second process deadline expired before collecting the whole control; its
receipt is retained. The retry changed only the outer process deadline, not
the 5,000-unit or 60-second per-law limits. Raw, decoded and per-call data are
in `results.json`, `tf1-control.log`, `tf1-deferred.log` and `tf1-calls.log`.
