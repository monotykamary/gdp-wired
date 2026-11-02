# Regulated workflows: laws about two runs, deadlines, clauses

ROADMAP.md section 4 names what regulated workflows (healthcare, insurance, banking compliance, KYC, privacy) need
beyond the approvals and workflows already reached: laws over two runs in the library on extracted code, deadlines
over the request's time, a trace from each law to the clause it answers, and a certificate an auditor can check
again. This note says what was built for each, what it claims and what it refuses.

## 1. Laws about two runs (`gdp-wired/relational`, core/relational.ts)

**The construction.** `twoRuns(a, b, {shared, stays, given, refusals})` builds one rule from two (or from one rule
twice). It works at the builders' level, not on the compiled machine, so the rule it returns is an ordinary rule:
- each run's state, maps, kinded values, flags and own inputs are renamed `a_x` and `b_x`;
- the params and inputs in `shared` keep their names, so both runs read the same value;
- the step is both runs' own steps, each reading its own state through its callbacks, unchanged.

Because the result is a rule, `proveRule` and `proveSteps` apply to it as they are: refutation by runs, the
invariant search, k-induction, the kernel's check, the Lean export and the interchange certificate. Nothing in the
construction is trusted: a proof is about the rule built. `core/relational.test.ts` runs the rule built beside its
two sides, request by request.

- **`stays`.** Where `stays` holds, run b doesn't take the request and keeps its state (Goguen and Meseguer's purge).
- **`refusals`.**
  - `'same'`, the default: a request one run refuses and the other takes is a difference the law is about. An error
    is seen as much as a value. Both runs then keep their state, and the state variable `split$` is set. The law
    "the two runs refuse the same requests" holds `split$` at 0.
  - `'assumed'`: only requests both runs allow are taken, which is cheaper.
- **The extracted code's refusals.** These are the rule's `assume`: a raise or throw in the code. They are compared
  this way. The kinds' own assumptions (a choice in range) hold in both runs and are not compared.

Three laws are built on it. Each returns the rule built, the laws and step laws that state it, and helpers:

| Law | The runs | What is the same |
| --- | --- | --- |
| `noninterference(rule, {secret, visible})` | Two runs of one rule. The requests and params are equal except the secret ones (their own `a_` and `b_` inputs and params). | Every visible field and result, after every step, and the refusals. |
| `isolation(rule, {owner, sees, results})` | Run a takes every request. Run b takes only tenant B's: those whose `owner` input is B, a new param. | B's cells of the maps in `sees`, the `results` after each of B's requests (a step law), and B's refusals. |
| `agreement(old, next, {visible})` | Two rules on the same requests, inputs and params shared by name. | The state they share by name (or `visible`) after every history, and the refusals. This is migration safety. |

**Proving: `proveTwoRuns(law, {invariants})`.**
- **The rule's own invariants.** These are an extraction's `invariants`. They are lifted to each run (`lift`, which
  renames a law's names as the run's) and proven with the law.
- **Helpers.** The helpers are "this other value is the same in both runs", for every value the law doesn't name.
  They are tried first, Houdini's way: the set is proven without the search, the helper a failed goal names is
  dropped, and the set is tried again.
- **Then the search.** What remains goes to `proveSteps` with its search.
- **What the helpers add.** A hidden value that later reaches the visible ones must be the same in both runs for the
  induction to go through. The helpers give that, at the cost of a few kernel calls without search.
- **What a refutation shows.** A refutation is a real run of the rule built: two runs side by side. The CLI prints it
  as calls of the code, the values that differ as `a | b`.

**The comment forms** (core/laws.ts, read by the CLI over the code's names, like any law):

```
# gdp: law the diagnosis stays private: diagnosis never reaches requests, status
# gdp: law one account's attempts never change another's: isolated by key [seeing storage, result]
# gdp: law v2 behaves as v1: agrees with LimiterV1 [on used]
```

- **`never reaches`.** The secrets are arguments, params or answered calls. The visible names are fields and results.
- **`isolated by`.** It names the argument that says whose call it is. A method without that argument is no tenant's
  call, so run b doesn't take it. `seeing` defaults to every map and every result, and splits itself into the maps'
  cells at B and the results of B's calls.
- **`agrees with`.** It names another class of the same target (file, package or crate) that the CLI read beside
  this one.

**What it doesn't take yet.** These are refused with the reason:
- histories (`log`, sums, queries);
- carried maps, lists and sequences;
- tables of nodes;
- a law with "there exists" lifted to two runs;
- a shared name of another kind in the two rules.

## 2. Deadlines over the request's time

- **What the extractors give.** They already read the clock as one input a step: `time.time()`, `Date.now()`,
  `Clock.millis`, `DateTime.utc_now`, `Instant::now()`.
- **What was missing.** A law could only compare that input with numbers in the clock's own units.
- **What a law can now say.** A duration in the law's text: `now - requests[rid].received < 30 days`.
- **What a duration is.** A whole number and a unit, read as a constant in the clock's units. The unit is per
  language: seconds for Python, Elixir and Rust; milliseconds for TypeScript, Java and Kotlin. Otherwise it is
  `clock = "s"` or `"ms"` in gdp.toml, or `--clock`.
- **In the library,** `duration('30 days', 's')` is the same constant.
- **TypeScript's clock.** A TypeScript class's `Date.now()` has no name in the extraction. Laws read it as `now`, as
  they already read Python's.

**Linear only.** A day is 86,400 s and a week 604,800 s. The request's time counts seconds, with no time zone, leap
second or daylight saving. So the arithmetic stays linear: an integer constant beside the clock. The kernel decides it
as any other linear term. These are refused, each with the reason:
- months, years and quarters, which have several lengths;
- a duration that isn't a whole number of the clock's units (500 ms on a clock of seconds).

**Business days** (core/calendar.ts) are counted over a calendar the person states once, in gdp.toml:

    [calendar]
    weekend = ["sat", "sun"]
    holidays = ["2026-11-26", "2026-12-25", "2027-01-01"]
    utc_offset = "-05:00"

- **In a law:** `now - received <= 10 business days` is "the business days after received's day, up to and including
  now's, are at most 10". The day of receipt doesn't count and the last day counts whole. The count is negative when
  now is before received. Only a difference of two times compares with business days. In the library,
  `businessDays(calendar, clock)` (`gdp-wired/laws`) gives the same count as a term.
- **The arithmetic.** It stays the kernel's own: linear, with one division by a week. The count up to a time's day is
  k·w + (the working weekdays up to its weekday) − (the listed holidays up to its day). Here w is the time's week, the
  weekday's terms are comparisons with 7D·w, and each holiday is one comparison with the time. The holidays form a
  balanced choice, one path per count, never 2^n.
  - **A law of the state** divides by the week with div$k, whose facts the kernel already has.
  - **A law of one step** can't read a function, and a deadline is a law of a step. So each time's week there is a key
    of the step law, under a guard that only ⌊y/7D⌋ meets: ∀w. 7D·w ≤ y < 7D·w + 7D → L. That is L at ⌊y/7D⌋, since
    the guard has one solution. A time that may be below 0 takes two keys, w⁺ − w⁻.
  - Nothing new is trusted. The certificate is the existing `stepLaws` kind, and Lean checks it like any other
    (below).
- **What runs check.** The run search reads a step law's keys from 0 up and would never meet a week near 2,900. So
  core/watch.ts reads a key scaled past the small ones (k·w, k ≥ 16, in a comparison) where that comparison turns:
  ⌊t/k⌋ and the keys beside it. The search from a counterexample also tries its other values (a map cell's time of
  receipt) as inputs. Both are untrusted: they only add what a run checks or tries.
- **What it doesn't model:** daylight saving (one fixed offset), holidays not listed (a year with no list has none), and
  half days. The calendar is a statement, like a citation. A deadline proven over it holds for that calendar only. A
  law that a request *is* answered by a deadline still needs the sweep below.

"Within 30 calendar days" is 30 days. "Within one month" must be restated in days, and that restatement is the
reader's call, recorded in the citation.

**What a deadline law claims.** The code only acts when it is called, so a deadline is a law of a step: whenever a
request comes at time `now`, the state the step leaves meets the deadline. Two examples:
- `now - received >= 30 days implies status != "open"` for the request's own record: the lazy escalation real code
  does;
- `status == "fulfilled" implies now - received < 30 days`: a request is only fulfilled within its deadline.

A sweep over every overdue record needs a loop over the map, which the readers don't take yet (lane D). The clock is
any time, not only one later than the last: as the TypeScript reader's note says, the proof covers every clock,
including one that goes back. A law about two attempts in a row (the lockout below) is a k-step law from the library
(`stepsLaw`), with `duration` for the constant.

## 3. Law-to-clause traces

- **The form.** `# gdp: cite <law name>: <the clause, as text>`, any number of them for one law, in any file of the
  target.
- **Where it shows.** The CLI prints each under its law (`cites: ...`), and `--json` carries it.
- **Certificates.** With `--cert <dir>`, each proven law's certificate is written as an interchange document
  (docs/interchange.md) whose `meta` holds the producer, the file, the rule, the law, its text, where it is stated and
  its citations.
- **Checked as it is made.** The certificate is checked by the kernel's `checkCertificate` as it is written. A
  certificate that doesn't check is not written.
- **Where meta goes.** `meta` is never read by a checker, and a round trip keeps it. A citation is therefore never part
  of what is trusted: it says which clause a law answers, never that the law is faithful to it. That judgment stays a
  person's.
- **Dangling citations.** A citation naming no law stated in the target is refused ("not read", exit code 2), so a
  renamed law can't silently drop its clause.
- **Drafted and signed.** `gdp-wired draft` asks a drafter for laws from a clause's text, reads each over the code's
  names, and prints its citation marked `[unreviewed: drafted by ...]`. A person signs it off as
  `[reviewed-by: <name>, <date>]`. `check --require-review` exits 2 while a law is cited unreviewed. The mark is text,
  like the citation: it says who signed, never that the law is faithful (DRAFTING.md).
- **In the library,** `certify(rule, laws, stepLaws, meta)` makes the same document for any rule. For a law about two
  runs, that rule is the one built. Lean checks the same document through interchange/lean.ts's path.

## 4. What is verified and what isn't

**Verified:**
- **`core/relational.test.ts`**, on Modal.
  - Each construction proves what holds and refutes what doesn't with a real pair of runs: noninterference, a leak, a
    refusal by the secret, per-user against global lockout isolation, a refactor against a moved boundary.
  - The rule built runs as its two sides do, step by step.
  - Durations and their refusals, and the citation reader.
  - The Python CLI case: three proven laws, the certificate read back and accepted by `checkCertificate`, the leak
    broken by two runs.
- **research/next** still proves and refutes as before: `run-relational.ts` and `run-isolation.ts` give the same
  verdicts, and core/compose.ts is unchanged.
- **The typecheck** (`tsc -p .`) is clean on every file changed.
- **The quick bar** (`bun gates/bar.ts --quick --cand gen/laneC --base ae36917 --only rw,f1,f2,g332,suite,onecpu`;
  `runs/bar/runs/6c9bc5482f0f-vs-ae369178e65d-quick-2026-10-301720`). Nothing gained or lost:
  - f1: no difference.
  - f2: one first-pass difference, noise after three reruns a side.
  - rw: no difference.
  - g332: 332 of 332, the search 8 s faster in sum.
  - suite: 236 of 236, the one more being the new `relational` job.
  - onecpu: no failures.
  - Size: core/ and kernel/ +38,459 bytes. relational.ts is 24.9 KB; laws.ts +8.5 KB; cli.ts +5.1 KB; kernel/
    unchanged.
  - Lint: the first bar run caught a lint (two switches not exhaustive), fixed before this one.
- **Lean.** Proven laws' certificates (two isolations and a window law), turned into one Lean
  file by `research/regulated/lean.ts`, are checked by Lean 4.34.0 against the twin, with the citations as comments:
  - 6 theorems (each law set and its step law);
  - `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` only, with no sorry;
  - 71 s on Modal, 4 vCPU.

  The commands:

      gdp-wired check <target> --cert <root>/<name>      # each target's verdicts, its certificates in <root>/<name>
      bun research/regulated/lean.ts <root> Certs.lean   # then lean Certs.lean against lean-kernel's library

**Business days and drafting (gen/laneHC):**
- **The count.** It is checked against a day-by-day walk of the calendar with JavaScript's Date: 3,200 pairs of
  times over four calendars (Sat–Sun at −05:00 and −14:00, Fri–Sat at +03:00, Sunday only at +14:00), on both clocks,
  with eight holidays including two on a weekend. The term's value and `count` agree with the walk on every pair.
- **Laws over the count.**
  - Built with the builders: a 14-calendar-day desk is proven within 10 business days. The law of one step is proven
    by the kernel alone; the law of the state, given its helper "under 14 days", also by the kernel alone. Within 9
    business days is broken by a run: from a request received on a Saturday, the tenth business day falls on the 13th
    calendar day.
  - Through the CLI, in Python, with the calendar in gdp.toml: 10 business days proven, 9 broken with a run. With no
    calendar the law is not read, with why.
- **Lean.** The CLI's two certificates of business-day laws (keys, guards and holidays) are checked by Lean 4.34.0
  against the twin: 4 theorems, `propext`, `Classical.choice` and `Quot.sound` only, 75 s on boat
  (`runs/regulated/lean1`).
- **Mutants and review.** Nine mutants of calendar.ts are killed by the tests. Two survived the first tests: a
  holiday read from the second after its midnight, and a week's guard one day wide. Both were killed once the tests
  read each holiday's midnight and each guard at its week alone (`runs/regulated/mut2`). A read-only review by
  gpt-6.1-terra found one more. A holiday before 1969-12-22 lost its weekday to JavaScript's negative `%`, making a
  count one too many: fixed and tested.
- **Drafting** (`DRAFTING.md`). One test covers the path:
  - an answer's laws are read over the code's names;
  - one naming a cell the code lacks is refused;
  - a kept law pasted with its citation is proven;
  - `--require-review` exits 2 until the citation is signed, then 0.

**The measure on real code (corpus/README.md): not met.** Eight targets in seven codebases were taken through the
CLI: SMART's client-py, CMS Blue Button (two), django-session-timeout, HAPI FHIR, Google's fhir-gateway, Fides and
Orejime. Each has 1 to 2 laws with their clauses, 11 laws in all. The readers refuse every target, so none of the 11
is decided. A scan of 40 healthcare and privacy repositories read 3 of 3,788 files, all trivial, and 1 of 1,108
Python functions read as decisions. Most of that code is stateless functions or state kept in a database or a
request. What would move it is the readers' reach, ranked in corpus/README.md: decisions beyond Python, state outside
the object, untyped records, datetime fields.

**Not verified, or not done:**
- **Runs aren't shortened.** A refutation's run is the first the search found, not the shortest.
- **No sweep.** A deadline over every overdue record at once needs a loop over a map, which the readers don't take
  yet.
- **Time is linear only.** Months and years are refused, not modelled; business days only over the calendar stated,
  one fixed offset from UTC.
- **Durations need a known clock.** The clock's unit is known for Python, Elixir, Rust, TypeScript, Java and
  Kotlin. Others need `clock` in gdp.toml.
- **What two-run laws don't take:** histories, carried lists or maps, nodes, and laws with "there exists" lifted
  to two runs. `agrees with` takes only another class of the same target.
- **Type parameters.** The reader doesn't read type parameters; a generic class is read at an instantiation only by
  replacing its type parameter first.
- **Faithfulness to the clause.** A citation is never checked: whether a law is faithful to its clause is a reader's
  judgment, and the law-to-clause trace only records which clause.
- **The kernel** is unchanged: no trusted code was touched. The two runs are an ordinary rule, and a certificate is
  the existing interchange kinds `laws` and `stepLaws`.
