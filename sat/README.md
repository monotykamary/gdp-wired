# gdp-wired sat: bit-vector laws without bv_decide

`bv_decide` hands a bit-blasted goal to CaDiCaL and checks its LRAT certificate in the kernel, but the check runs as
compiled code (`Lean.ofReduceBool`, a native axiom). Here the same laws are bit-blasted, solved and checked in the
library; the trusted part is `lrat.ts` (or `check.ts`, which needs no hints). Lean's own LRAT checker can check the same
certificates, an optional path (`lean-lrat.ts`).

| File | What it is |
| --- | --- |
| `cnf.ts` | A bit-blaster: and/or/xor/ite gates, Tseitin-encoded as built (with constant folding); bit-vectors with shifts, and/or/not, eq, ripple add, ult/ule |
| `solver.ts` | CDCL over an Int32Array clause arena (literals coded 2v / 2v + 1): two watched literals with blockers, binary clauses watched by their other literal alone, first-UIP learning with recursive minimization, VSIDS on a binary heap with phase saving, glucose-style restarts (the recent LBD average 1.25× the long one; Luby with `restarts: 'luby'`), LBD-ordered deletion of learned clauses (dropped from the watch lists at once). A model, or a refutation twice over: a DRUP proof (lemmas, deletions as `{d: clause}`, the empty clause; `drup: false` skips it) and the same proof as LRAT (every clause an id; each lemma names its hints: level-0 units, the reasons reached from the conflict outside the lemma in trail order, the conflicting clause), trimmed to the lemmas the empty clause uses. Or `unknown` past a conflict budget. `solver-v1.ts` is the previous version (arrays of arrays, a linear scan per decision), kept for comparison |
| `lrat.ts` | Trusted, 50 lines: an LRAT proof refutes the CNF when each lemma, with its literals false, makes its hints unit one by one until one is falsified; no search, so a check costs the hints' lengths. Lemma ids increase; deletions by id |
| `check.ts` | The trusted part: a model satisfies every clause; a DRUP proof checked backward (the empty clause first, then only the lemmas its conflicts used, in reverse, core clauses propagated first) or forward (every lemma); deletions honoured |
| `solver.test.ts` | Random 3-SAT against brute force and near the threshold, with and without the solver's options, every answer checked by all three checkers; PHP(6, 5), PHP(8, 7); proofs of a satisfiable formula (real and tampered) rejected; deletions; LRAT tampering (a wrong, dropped or reordered hint, a negated literal, a dropped lemma, a reused id) and refutations found before any decision |
| `lean-lrat.ts` | The optional Lean path: writes the CNF as Lean data and the LRAT certificate as text, and `theorem unsat : cnf.Unsat := LRAT.check_sound proof cnf (by native_decide)` (or `decide +kernel`), with Lean's checker from `Std.Tactic.BVDecide.LRAT`, the one bv_decide uses; a tampered copy must compute to `false` |
| `run-bv.ts` | The k = 31 and k = 64 laws of `../lean/ProbeBv*.lean` proven, the false variant refuted with w decoded (w = 3, as bv_decide found); small adder identities |
| `one-problem.ts` | One benchmark problem, solve only, for tuning sweeps (`TUNE='{"lubyUnit":512}'`, `RESTARTS=luby`) |
| `bench.ts`, `ablate.ts` | Harder problems (adders, ult transitivity, shift-and-add multipliers, pigeonhole): solve, proof size, forward vs backward check; the solver with and without minimization and deletion |
| `lean-probes.ts` | The same problems as Lean files for bv_decide, for wall-time comparison |

```sh
bun test solver.test.ts
bun run-bv.ts
bun bench.ts [conflict budget] [name regex]     # CHECKS=lrat,backward,forward picks the checkers; SOLVER=v1, RESTARTS=luby, TUNE=<json>
bun one-problem.ts "10 bits"                     # solve only
bun lean-lrat.ts '<name regex>' <dir> native|kernel && lean <dir>/*.lean
bun ablate.ts "PHP(9" "× b = b × a, 8"
bun lean-probes.ts <dir> && (cd <dir> && for f in *.lean; do LEAN_PATH=$TC/lib/lean $TC/bin/lean $f; done)
```

Canonical timings from Modal (2 vCPU x86_64 containers, one job per cell, two runs per row,
`runs/modal-jobs/speed-final.json`); the full table, the tuning sweep and round 3's (with Lean's own checker) are in
`runs/sat-bench.md`. bv_decide is `lean` wall time for its probe, including the ~0.8 s import; its SAT step is native
CaDiCaL, its LRAT check compiled (`Lean.ofReduceBool`).

| problem | solve, v1 | solve, v2 | lemmas kept by LRAT trim (v2) | DRUP forward | DRUP backward | LRAT (`lrat.ts`) | bv_decide |
| --- | --- | --- | --- | --- | --- | --- | --- |
| a + b = b + a, 32 bits | 0.06–0.07 s | 0.02–0.03 s | 987 | 0.02–0.04 s | 0.02–0.03 s | 0.01 s | 0.8 s |
| (a + b) + c = a + (b + c), 16 bits | 0.11 s | 0.07–0.08 s | 2,936 | 0.14–0.21 s | 0.09–0.11 s | 0.01 s | 0.9 s |
| a < b, b < c ⇒ a < c, 32 bits | 0.8–1.4 s | 0.01 s | 474 | 0.01 s | 0.01 s | 0.00 s | 0.8 s |
| a × b = b × a, 6 bits | 0.11 s | 0.06 s | 2,249 | 0.15 s | 0.12 s | 0.01 s | 1.4 s |
| a × b = b × a, 8 bits | 4.0–5.2 s | 1.27–1.35 s | 41,499 | 17.6–22.1 s | 12.7–17.0 s | 0.18–0.22 s | 2.3 s |
| a × b = b × a, 10 bits (16 GB) | 150–204 s | 29–37 s | 548,814 (63.7M hints) | not run | not run | 3.9–4.1 s | 23.9 s |
| a × b = b × a, 12 bits (64 GB) | no answer in 9.5 min | **735 s** | 8,447,981 (1.31 billion hints) | not run | not run | **67.7 s** | timeout at 389 s (heartbeats) |
| PHP(7, 6) | 0.02 s | 0.02 s | 1,019 | 0.04 s | 0.02–0.03 s | 0.00 s | 0.8 s |
| PHP(8, 7) | 0.27 s | 0.11–0.13 s | 6,045 | 0.46–0.51 s | 0.31–0.34 s | 0.02 s | 1.2 s |
| PHP(9, 8) | 1.3–1.8 s | 0.78–0.84 s | 25,801 | 7.4–8.0 s | 4.5–4.7 s | 0.04–0.05 s | 1.1 s |
| PHP(10, 9) | 17.4 s | 3.8–4.5 s | 96,754 | not run | 48.6–50.6 s | 0.18–0.29 s | 2.3 s |

The rewrite (round 4) made the solver 2–6× faster on the hard rows, and checking stays cheap: LRAT takes 1–10% of the
solve. Solve plus check now beats bv_decide on the 8-bit multiplier and PHP(9, 8), is 1.6× slower on the 10-bit
multiplier (it was 8.5×), and answers the 12-bit multiplier, which bv_decide doesn't. Lean's own checker accepts our
certificates (`native_decide`, so `Lean.ofReduceBool` as with bv_decide); `decide +kernel` didn't finish PHP(7, 6) in
about 10 minutes.