# Three ways to state and prove the same laws

The same three stateful rules, with the same laws, written three ways:

- **gdp-wired**: this library's typed builders (`core/dsl.ts`), proven with `proveRule`.
- **Bend 2**: the Bend repo's language (`bend2/`), with `law`s and hand proofs, checked by `bend` and rechecked with `bend --verdict`.
- **plain Lean 4.34.0**: core Lean only (no Mathlib, nothing from gdp-wired), with theorems proven by hand using `induction`, `split` and `omega`.

| Rule | Semantics | Law |
| --- | --- | --- |
| budget | s starts at 0; a request of cost c sets s to s + min(c, m) when s < b, and leaves s alone otherwise | s ≤ b + m after any sequence of requests |
| caps | a request (acct, day, ok) is granted iff ok, its acct has no grant yet, and its day has fewer than d grants | at every key, grants per acct ≤ 1 and grants per day ≤ d |
| window | a request (forced, t) is admitted iff it is not forced and seen + 1 ≤ c, where seen counts the logged requests with t < r.t + w; forced requests always go through; both kinds are logged | at every `now`, the admitted (unforced) logged requests with r.t ≤ now < r.t + w number at most c, for every history |

| | budget | caps | window |
| --- | --- | --- | --- |
| gdp-wired | [`gdpwired/budget.ts`](gdpwired/budget.ts) | [`gdpwired/caps.ts`](gdpwired/caps.ts) | [`gdpwired/window.ts`](gdpwired/window.ts) (the builder form of `core/models.ts`'s `windowLimit`) |
| Bend 2 | [`bend/budget.bend`](bend/budget.bend) | [`bend/caps.bend`](bend/caps.bend) | [`bend/window.bend`](bend/window.bend) |
| Lean 4 | [`lean/Budget.lean`](lean/Budget.lean) | [`lean/Caps.lean`](lean/Caps.lean) | [`lean/Window.lean`](lean/Window.lean) |

Each file stands alone, so the Bend files repeat the `LE`/`Cmp2`/`dec` block and the `≤` lemmas they need. Each file is
split by marker comments: `--- rule`, `--- laws`, `--- proofs` and `--- run` (a small demo run, not counted). Bend has
one more marker, `--- evidence`, explained below. In Bend and Lean, `ours`, the count the window law talks about, sits
under laws. In gdp-wired it is a `.sums` declared in the laws section.

## Numbers

All of these come from one Modal run, `runs/modal/compare/final/`
(`compare.log`, `gdp-lean-twin.log`, `typecheck.log`). Every job ran in its own container with 2 CPUs, the same image
for all three tools (bun 1.4.3, Lean 4.34.0), and the Bend repo's `bend2/` mounted beside gdp-wired. [`run.ts`](run.ts)
counts lines that are neither blank nor a whole-line comment, section by section. "check" is the wall time of the
whole command, the median of 5 runs: `bun gdpwired/<rule>.ts` (prove, kernel check, a short compiled run), then
`bun bend2/main.ts <rule>.bend --check-only` or `--verdict`, then `lean <Rule>.lean`. "broken variant" means each tool
was also given the same bug and had to reject it. The budget forgets the m cap. The day cap is off by one (≤ d
instead of < d). The window admits when seen ≤ c instead of seen + 1 ≤ c.

| tool | rule | rule lines (of which evidence) | law lines | proof lines | check, median ms | checked | broken variant rejected |
| --- | --- | --- | --- | --- | --- | --- | --- |
| gdp-wired | budget | 5 | 1 | 1 | 25 | yes | yes |
| gdp-wired | caps | 6 | 4 | 1 | 44 | yes | yes |
| gdp-wired | window | 7 | 2 | 2 | 42 | yes | yes |
| bend | budget | 39 (25) | 5 | 84 | 137 | yes | yes |
| bend | caps | 98 (50) | 10 | 74 | 161 | yes | yes |
| bend | window | 63 (31) | 26 | 117 | 156 | yes | yes |
| bend --verdict | budget | 39 (25) | 5 | 84 | 167 | yes | yes |
| bend --verdict | caps | 98 (50) | 10 | 74 | 178 | yes | yes |
| bend --verdict | window | 63 (31) | 26 | 117 | 174 | yes | yes |
| lean | budget | 4 | 1 | 8 | 488 | yes | yes |
| lean | caps | 15 | 2 | 30 | 547 | yes | yes |
| lean | window | 13 | 4 | 29 | 571 | yes | yes |

How to read the times:

- **Startup floors.** These are medians with no rule at all: gdp-wired 17 ms (bun loading `core/dsl.ts`), bend
  134 ms (a file that only imports Base), bend --verdict 152 ms, and lean 453 ms (an empty file). Most of each check
  time is this floor. The rules themselves add about 8 to 27 ms in gdp-wired, 3 to 27 ms in Bend, and 35 to 118 ms in
  Lean.
- **gdp-wired, in process.** Timed inside the process, `proveRule` takes 8.5 ms for budget, 21.0 ms for caps and
  21.6 ms for window. Each figure covers growing the proof trees and the kernel's check.
- **One-time costs.**
  - Bend: the first `--verdict` builds BendTT's Lean kernel, which took 30.6 s. The build is cached under
    `~/.bend/bendtt/` and is not included in the table.
  - gdp-wired's Lean twin: building `lean-kernel/`'s Cert, Kernel, Progress and History `.olean` files took 11.9 s,
    once.
- **gdp-wired's optional Lean twin on these exact rules.** [`twin.ts`](twin.ts) runs `lean-kernel/export-kernel.ts
  --examples ../compare/domain.ts`, which writes the kernel's trees for all three rules ([`domain.ts`](domain.ts)) as
  138 lines of Lean data. `lean Compare.lean` then checked `compare_0_laws` (budget), `compare_1_laws` (caps) and
  `compare_2_laws` (window) in 1.35 s (`runs/modal/compare-twin/`), through `Kern.machine_sound`, `fmmachine_sound`
  and `hmachine_sound`. The axioms used were `propext`, `Classical.choice` and `Quot.sound`.
- **Typecheck.** `tsc -p compare` passes on the gdp-wired files, `run.ts` and `twin.ts` (2.9 s).

How hard each one was to get checked, from the Modal logs of the attempts: the gdp-wired and Lean files checked on
their first run. The only Lean edit afterwards renamed the deprecated `if_pos` and `if_neg` to `ite_eq_left` and
`ite_eq_right`. `bend/caps.bend` checked on its first run. `bend/budget.bend` and `bend/window.bend` each needed one
affinity fix: a pattern variable that is used twice must be written with `+` (`1n++p`, `Con{x, +r}`).

## What each one proves, and how

**gdp-wired.**

- *What the rule is.* A rule is a step machine over naturals. The step can use linear arithmetic, truncated
  subtraction, min and max, if/then/else, and products. It can also use maps with one write per step, and histories
  with sums and queries over the log.
- *How it is proven.* `proveRule` turns each law into obligations: the law holds at the start, and one step preserves
  it (`kernel/kernel.ts`). Laws stated with `forall` are proven at a fresh key and assumed at the keys the step reads.
  An untrusted prover (`kernel/prove.ts`) grows a tree of case splits that ends in linear refutations, and the trusted
  kernel (`kernel/kernel.ts` with `core/check.ts`) checks that tree.
- *What the user writes.* There is no proof to write: the induction over every sequence of requests is the kernel's
  own rule. The one exception is the window, which needs a single relation, `ours ≤ seen whenever t ≤ now`. The
  kernel proves it for one record and then assumes it at every step (`kernel/README.md`, "histories").
  - Without that relation the window law is refuted (`core/dsl.test.ts`, the "variants" test).
  - Finding that relation is the one real proof idea here. Bend's `le_seen` and Lean's `le_seen` are the same idea.
- *The limit.* You can only state what the machine language expresses. Invariants of a step machine fit; functional
  correctness of arbitrary code does not.

**Bend 2.**

- *What a law is.* A law is a type that mentions the program's own functions (`run`, `step`, `count_acct`, `ours`),
  and a proof is a def of that type. All three laws quantify over every request list, and each proof is a structural
  induction written by hand (`run_ok`, `acct_run`/`day_run`).
- *No tactics.* Bend has no tactics and no arithmetic decision procedure. Every fact about `≤` is a lemma proven by
  hand by recursion on `Nat`: `le_trans`, `le_succ`, `le_add`, `add_le_l`/`add_le_r`, `add_le2`, `min_le` and
  `no_succ_le`. That is most of the 74 to 117 proof lines.
- *Why the rules carry evidence.* A Bend match inspects a parameter, never a computed value (GUIDE.md, "Recursion and
  Termination"). So a proof cannot case-split on `s < b` the way Lean's `split` does.
  - The idiomatic workaround is the one Bend's insertion-sort flagship uses (`tests/proof/insertion_sort_sorted.bend`):
    the program branches on a comparison that carries its evidence (`Cmp2`: `IsLe{LE(x, y)}` or `IsGt{LE(1 + y, x)}`;
    `Same`: `Hit{a == k}` or `Miss`). Each proof then follows the same chain of helper defs as the step.
  - The `--- evidence` section holds that support code, and it is counted as rule code: 25 to 50 lines per file.
  - Writing the step this way is also why one rule becomes several small defs (`step.ok`, `step.acct`, `step.day`).
- *The upside.* The laws are about the exact code that compiles and runs. Bend can state anything its dependent types
  can express.

**Plain Lean 4.**

- *How the proofs go.* The proofs have the same shape as Bend's: generalize the start state, induct on the request
  list, and split on the step's `if`.
- *Why they are short.* `omega` closes the arithmetic, and `if` conditions can be split on directly. That makes the
  proofs 8 to 30 lines with no hand lemmas about `≤`, and the rules read as ordinary functions.
- *The cost.* Every invariant and its induction is still written by hand. In Caps, the per-account proof and the
  per-day proof are near copies of each other.
- *Scope.* Lean is the most general of the three. It can state and prove anything, with Mathlib if needed.

## What each one gives at runtime

| | what runs | size from this run | numbers |
| --- | --- | --- | --- |
| gdp-wired | `compileJs` (`core/machine.ts`) makes a JS module with `init`, `fork` and `step` from the same `Machine` the kernel proved; `.compiled()` loads it | 1,116 / 1,540 / 1,966 bytes of JS (budget / caps / window) | JS numbers, checked to stay below 2^53 at every step (`$n`, `$x`): past that the proofs over ℕ would no longer describe the run. The log stays in place, and queries are computed by the runtime |
| Bend 2 | the proven functions *are* the program: `bend -o x.js` runs `main`, `bend -o x.mjs` exports the non-IO defs (`step`, `run`) for JS to import, and `bend -o x` builds a native binary (CPU threads and GPU from one C file) | `.js` 14,625 / 16,646 / 15,642 bytes, `.mjs` 11,756 / 13,711 / 16,101 bytes (both with the runtime included); each `.js` printed the same demo result as the checker | `Nat` compiles to a checked 64-bit word (`bend2/comp.ts`). The comparison evidence (`IsLe`/`IsGt`, `Hit`/`Miss`) is real data at runtime |
| Lean 4 | `lean -c` emits C for the definitions; running it means building with Lean's runtime (`lake`/`leanc`). Core Lean has no JS target | 3,305 / 8,473 / 8,775 bytes of C | `Nat` is arbitrary precision |

The demo runs agreed across all three tools: budget s = 12; caps granted (1,5) and (2,5) and refused the rest; the
window logged 3 of 5 requests. The broken variants also showed their bugs at runtime: the off-by-one caps rule
granted a third grant on day 5 in both gdp-wired and Lean, and the broken window logged 4 requests.

## Running the rules

Each tool runs the code it proved over a stream of N requests, and prints a checksum of the final state. The Bend and
Lean programs are the compare files unchanged up to `--- run`, with a main that takes N in place of the demo
([`bench/bend/`](bench/bend/), [`bench/lean/`](bench/lean/); [`bench/run.ts`](bench/run.ts) checks the prefix).
gdp-wired's [`bench/gdpwired.ts`](bench/gdpwired.ts) imports the rules from `gdpwired/` and steps `.compiled()`.

- **The stream.** The LCG x' = (x * 1103515245 + 12345) mod 2^31, from x = 42, one step per request, with each
  request's fields read off the new x the same way in all three languages.
  - budget: c = x mod 16, with b = 8N and m = 10. b is never reached (s ends near 6.6N), so every request adds.
  - caps: acct = x mod 1000, day = x mod 365, ok = x mod 4 ≠ 0, with d = 3. acct and ok share x mod 4, so accounts that
    are multiples of 4 are never granted, and the grants stop at 750.
  - window: t grows by x mod 3 from 0, forced = x mod 10 = 0, with w = 60 and c = 5.
- **The checksums.** budget prints s. caps prints the grants, the sum of their accts and the sum of their days. window
  prints the logged requests, how many were forced and the sum of their t. The three tools printed the same checksum at
  every N they ran.
- **The commands.**
  - gdp-wired: `bun compare/bench/gdpwired.ts <rule> N`.
  - Bend: a native binary from `bend <rule>.bend -o <rule>` (the C runtime, built with Debian's clang 14), run as
    `./<rule> N`.
  - Lean: `lean -c <Rule>.c <Rule>.lean`, then the toolchain's `leanc -O3`, run as `./lean_<rule> N`.
  - Builds took 1.0 to 1.5 s for Bend and 2.3 to 3.8 s for Lean (`lean -c` also checks the theorems). They are not in
    the table.

All of these come from one Modal run, `../runs/modal/compare-bench/v1/` (beside the gdp-wired checkout). Each rule
ran in its own container with 2 CPUs, on the same image as above. The times are the wall time of the whole command,
the median of 3 runs. N = 0 is each tool's startup floor. A run past 300 s was stopped.

| rule | N | gdp-wired ms | Bend ms | Lean ms | checksum |
| --- | --- | --- | --- | --- | --- |
| budget | 0 (floor) | 27 | 2 | 4 | 0 |
| budget | 1,000 | 29 | 12 | 5 | 6558 |
| budget | 10,000 | 32 | 923 | 6 | 65625 |
| budget | 100,000 | 44 | 92,391 | 8 | 656250 |
| caps | 0 (floor) | 31 | 3 | 7 | 0 0 0 |
| caps | 1,000 | 36 | 343 | 8 | 452 231196 81141 |
| caps | 10,000 | 36 | 7,361 | 26 | 748 374281 133771 |
| caps | 100,000 | 59 | 75,122 | 205 | 750 375000 134095 |
| window | 0 (floor) | 31 | 3 | 5 | 0 0 0 |
| window | 1,000 | 32 | 62 | 6 | 120 98 56848 |
| window | 10,000 | 64 | 50,795 | 82 | 1189 1028 5944251 |
| window | 100,000 | 2,572 | stopped at 300 s | 8,740 | 11745 10107 587008768 (gdp-wired, Lean) |

The state each one keeps, which decides most of these numbers:

| | budget | caps | window |
| --- | --- | --- | --- |
| gdp-wired (generated JS) | one number | two `Map`s from key to count (`Acct`, `Day`). A step reads and writes one cell of each | an array of every logged request. Each step scans all of it for `seen`, because this rule declares no `.prune`, so the log is never pruned |
| Bend | one `Nat` | a list of every grant. `count_acct` and `count_day` scan it | a list of every logged request. `seen` scans it |
| Lean | one `Nat` | the same list as Bend | the same list as Bend |

How to read the times:

- **gdp-wired.** Most of each time is the floor, which is bun loading `core/dsl.ts` and the rule and compiling the
  step. The window's unpruned log is the only state that grows, and at 100,000 requests each step scans up to 11,745
  records.
- **Bend.** `Nat` is a 64-bit word, and Base's `Nat.add` and `Nat.min` compile to machine operations. The comparisons
  the proofs case on (`dec` and `same`, in `--- evidence`) are ordinary recursions, though. They take one off each
  argument per call, so a comparison costs as many calls as the smaller number.
  - budget: `dec(b, s)` costs about s calls per request, so the run is quadratic in N. 10 times the requests took 100
    times as long.
  - caps: `same(a, k)` costs up to 999 calls for each of up to 750 grants, for every request.
  - window: `dec(e.t + w, t)` costs about t calls for each logged request. t grows with N, so the run is cubic. At
    N = 100,000 the first run did not finish in 300 s.
- **Lean.** `Nat` comparisons are constant time on small values. What grows is the list scans: up to 750 grants per
  caps request, and the whole log per window request.
- **What this measures.** This is the cost of running each rule as it was written to be proven. gdp-wired's runtime
  representation comes from the machine, not from how the law is written. A Bend or Lean rule written for speed (maps,
  or a pruned log) would need its proofs redone.

### Bend's GPU path

A rule's run is a fold over the requests, each step needing the state the one before left, so there is no parallel
work for a GPU. To check that anyway, [`bench/gpu.ts`](bench/gpu.ts) hands each rule's run to the GPU (`run!(...)` in
place of `run(...)` in the bench's entry point, the rule and its proofs unchanged), builds it with CUDA 12 and clang 19,
and times it beside the plain CPU binary and beside the same binary with its GPU off (`--gpu off`, which runs the `!`
call on the CPU lanes). [`bench/modal_gpu.py`](bench/modal_gpu.py) runs it on a Modal L4 (`runs/modal/compare-bench/gpu/`):

| rule | N | CPU binary ms | `run!` binary, `--gpu off` ms | `run!` binary, GPU on |
| --- | --- | --- | --- | --- |
| budget | 0 | 4 | 14 | did not return in 300 s |
| budget | 1,000 | 11 | 20 | |
| budget | 10,000 | 693 | 645 | |
| caps | 0 | 4 | 14 | did not return in 300 s |
| caps | 1,000 | 186 | 195 | |
| caps | 10,000 | 3,719 | 3,754 | |
| window | 0 | 4 | 14 | did not return in 300 s |
| window | 1,000 | 50 | 52 | |
| window | 10,000 | 38,204 | 31,877 | |

Every run printed the CPU benchmark's checksum. With the GPU on, nothing returned, even with no requests. The guide's
own parallel example (`pow2!(20n)`, `PROBE=1`) does the same on this image: its GPU program builds, `--gpu off` prints
1048576 in about 20 ms, and with the GPU on it does not return in 60 s, on an L4 and on an H100 alike. So Bend's CUDA
path does not run in these containers, for reasons that have nothing to do with these rules. The `--gpu off` column is
what the `!` costs a serial fold on the CPU: about 10 ms more startup, otherwise the same.

## Trust bases

- **gdp-wired.**
  - *What is trusted.* `kernel/kernel.ts` (455 lines: goal building, scope check and tree check) and
    `core/check.ts` (33 lines: replaying a linear derivation). `core/dsl.ts` and `kernel/prove.ts` are untrusted:
    the kernel checks whatever they hand it.
  - *Not verified.* That `compileJs` runs the semantics the kernel reasons about. It is backed by tests
    (`core/conformance.test.ts`, `core/runtime.test.ts`), not by proof.
  - *The optional Lean twin.* `lean-kernel/` (Kernel.lean, Progress.lean, History.lean and Cert.lean, 3,332 lines)
    re-checks the trees and builds the induction goals in Lean. Its soundness theorems are proven, using `propext`,
    `Classical.choice` and `Quot.sound`. After that, the trust is in Lean's kernel and in the exported machine data
    (`twin.ts` / `export-kernel.ts` produce it unverified, so read it to confirm it is your rule).
- **Bend 2.**
  - *Plain `bend`.* Trusts the checker `bend2/bend.ts` (3,882 lines).
  - *`--verdict`.* Also rechecks every def with BendTT's kernel `bend2/bendtt.lean` (3,981 lines). Its claims are
    proven in Lean: no checked def has type Empty, and live code halts. The elaborator `bend2/safe.ts` (1,673 lines)
    that translates to BendTT has no proof (GUIDE.md: "read it to confirm a law").
  - *Not verified.* The compiler `bend2/comp.ts`, which turns the checked program into C or JS.
- **Lean 4.**
  - *What is trusted.* Lean's kernel. `omega`, `simp` and `split` build proof terms that the kernel checks.
  - *Not verified.* The compiler, which is separate from the kernel.

## Where each one is the better tool

- **gdp-wired:**
  - The rule fits its machine language, which covers counters, caps, budgets, maps with per-key laws, and logs with
    window counts.
  - You want the proof without writing one: each law here is a one-line statement and a `proveRule` call.
  - You want the rule shipped as small, dependency-free JS that comes from the same object the kernel proved.
  - You want broken variants rejected in milliseconds with a counterexample, which suits iterating on a policy.
  - The Lean twin is there when a second, independent check is wanted (1.1 s for these three rules).
  - *Its limit:* a law outside the language cannot be stated at all.
- **Bend 2:**
  - You want the laws to be about the exact program that runs, including on CPU threads, on GPUs and as JS, with no
    gap between model and code.
  - You want a language general enough for any property, with a proof-checked kernel behind `--verdict`.
  - *The price, in this comparison:* 74 to 117 proof lines per rule against gdp-wired's 1 or 2, plus 25 to 50 lines of
    evidence-carrying rule code. Without tactics or `omega`, arithmetic facts are lemmas you write.
- **Plain Lean 4:**
  - You need full generality with the least proof effort per law, since `omega` absorbs the arithmetic.
  - You want the mathematical result itself rather than a deployed rule.
  - You accept writing every induction yourself, a slower check (most of it Lean's 0.45 s startup), and no JS output.

## Running it

[`modal_compare.py`](modal_compare.py) is modeled on `modal/run.py`. It mounts gdp-wired and the Bend repo's `bend2/`
(from `$BEND_REPO`, default `../bend`, read-only), registers its app in `modal/.live/`, and cancels its calls on exit.
[`jobs.json`](jobs.json) has three jobs: `run.ts` (the table), the Lean twin, and the typecheck.

```sh
cd gdp-wired && modal run compare/modal_compare.py --jobs compare/jobs.json --out runs/modal/compare/final && sh modal/reap.sh
```

The runtime bench has one job per rule in [`bench/jobs.json`](bench/jobs.json), and each job installs clang for
Bend's native build:

```sh
cd gdp-wired && modal run compare/modal_compare.py --jobs compare/bench/jobs.json --out ../runs/modal/compare-bench/v1 && sh modal/reap.sh
```

One rule locally: `BEND=/path/to/bend bun compare/bench/run.ts caps` (`RUNS=3`, `NS=0,1000,10000,100000` and
`LIMIT=300` seconds per run by default).

`run.ts` alone, where bun, Lean 4.34.0 and the Bend repo are: `BEND=/path/to/bend bun compare/run.ts` (`RUNS=5` by
default).
