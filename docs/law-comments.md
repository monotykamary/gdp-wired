# Laws in code comments

What a `gdp: law` comment may say, in every language the CLI reads. The contract behind it (the forms, how each is
read, what is refused) is in [FRONTENDS.md](FRONTENDS.md#the-clis-comment-law-contract).

## Where the comment goes

`//` in Go, Rust, C, C++, Java, Kotlin and TypeScript (an Effect service's laws above its make effect, an XState
machine's over its context, `value` and `event`); `@GdpLaw("<name>: <expr>")` on a Java or Kotlin method (with
the annotation declared in your code), `@gdp_law("...")` in Python, `@gdp_law "..."` in Elixir, `#[doc = "gdp: law
..."]` in Rust. The expression: comparisons, `+ - * k`, `and or not implies`, the state after the step by its fields
(`self.`, `this.`, `@` or bare; `after.x`), `old(x)` or `before.x` before it, the request's arguments by name,
`result`, `failed`, a call of other code answered by the request as `f(...)`, `x is None`, maps as the code reads them
(`counts[user]`, `user in counts`, `cache["rl:" + user]`), `forall k in m: ...`, a choice by its value (`mode ==
"closed"`). Anything else is refused with why, never dropped. Modelling choices a rule needs (`failures = "kept"` for
laws about when it raises, a store's attributes, an untyped result) go in a `gdp.toml` beside the code (or `[tool.gdp]`
in pyproject.toml, `"gdp"` in package.json), per rule under `[rules.<name>]`. When an individual stated invariant or step
law ends `unknown` (neither proven nor refuted) in default reachable-state `check`, it is retried jointly with the other
laws stated on the same rule within the time its own budget has left, crediting only that law and only if the kernel checks
the whole joint family (never changing a proven or refuted verdict). The exit code is 1 when a stated law is
broken, 2 when one couldn't be checked: `uses: monotykamary/gdp-wired@main` with `paths:` runs it in CI.

## Two runs, durations and citations

Laws about two runs read the same way: `diagnosis never reaches status, result` (two runs differing only in the
secret keep what is named the same, and fail alike), `isolated by user_id` (what the caller whose `user_id` is B sees
is the same whatever the others do), `agrees with LimiterV1` (a migration: another class of the target, the same state
after every history). A duration is linear over the request's time: `now - received < 30 days` (seconds, minutes,
hours, days, weeks; a month or a year is refused). Business days are counted over a calendar stated once (`[calendar]`
in gdp.toml: weekend days, holidays, a UTC offset): `now - received <= 10 business days`, decided in the same linear
arithmetic, nothing trusted added. `gdp: cite <law name>: <clause>` ties a law to the clause it answers: printed with
the law, and with `--cert <dir>` kept in the meta of each proven law's certificate, never in what is checked.
`gdp-wired draft <file> --clause-file <f> --cite <ref> --llm <command>` asks a drafter (a model, by any command) for
laws from the clause's text, reads each over the code's names and prints the comments to paste, each citation marked
`[unreviewed: drafted by ...]` until a person signs it (`[reviewed-by: <name>, <date>]`); `check --require-review`
refuses a law cited unreviewed (`research/regulated/DESIGN.md`, `research/regulated/DRAFTING.md`).
