# LiteLLM's budgets, session limits and cooldown, read from its Python

Seven of LiteLLM's rules, extracted from the code that ships by `gdp-wired/extract-py` (core/extract-py.ts, on the shared
step executor of research/langs/DESIGN.md), each checked against LiteLLM's own code by running both, and their laws
proven of the extracted rule. Nothing here is written by hand but the laws: the rules are what the code does.

| Item | Reads (module: functions) | What it states about the rest |
| --- | --- | --- |
| `quota/litellm-py/virtual_key_max_budget_check` | `litellm/proxy/auth/auth_checks.py`: `virtual_key_max_budget_check` | the spend counter (`get_current_spend`) and the over-budget throttle (`_apply_budget_exceeded_throttle`) answered by the request; the alert and the error message left out |
| `quota/litellm-py/team_max_budget_check` | `auth_checks.py`: `team_max_budget_check` | the spend counter answered |
| `quota/litellm-py/_project_max_budget_check` | `auth_checks.py`: `_project_max_budget_check` | the spend counter answered |
| `quota/litellm-py/check_end_user_budget` | `auth_checks.py`: `check_end_user_budget` | the spend counter and `RouteChecks.is_info_route` answered |
| `rate limit/litellm-py/MaxIterationsHandler` | `litellm/proxy/hooks/max_iterations_limiter.py`: `__init__`, `async_pre_call_hook`, `_make_cache_key`, `_increment_and_get`, `_in_memory_increment` | the internal usage cache as a store with Redis off (the in-memory path), its TTL left out; the session id and `max_iterations` answered |
| `quota/litellm-py/MaxBudgetPerSessionHandler` | `litellm/proxy/hooks/max_budget_per_session_limiter.py`: `__init__`, `async_pre_call_hook`, `_make_cache_key`, `_get_current_spend` | the cache as a store, Redis off, read only (every spend it may hold); the session id and the budget answered |
| `circuit breaker/litellm-py/should_cooldown_based_on_allowed_fails_policy` | `litellm/router_utils/cooldown_handlers.py`: `should_cooldown_based_on_allowed_fails_policy` | the fleet-wide fail counter (`_increment_allowed_fails`) and the router's per-exception policy (`Router.get_allowed_fails_from_policy`) answered |

The laws are in `specs.ts`, written against the extracted rule's names (the code's own: a parameter's, a field's, an
answered call's), so the same law runs unchanged on a fork whose functions keep their signatures.

## Use it on your fork

You need Bun, this repository, and a Python that imports your fork (LiteLLM's proxy extras installed):

```sh
git clone https://github.com/<you>/litellm my-litellm && cd my-litellm && git checkout <your branch or tag>
python3 -m venv .venv && . .venv/bin/activate && pip install -e '.[proxy]'          # the code the check runs
cd <gdp-wired> && bun install
bun research/langs/litellm/run.ts --src ../my-litellm --python ../my-litellm/.venv/bin/python
#   --only '<item id>' for one item, --ms 60000 the search per law, --json out.json for the verdicts
```

On Modal instead (nothing installed locally; about 3 minutes and a few cents): set the repository and ref and run the
job, then reap.

```sh
LITELLM_REPO=https://github.com/<you>/litellm LITELLM_REF=<branch or tag> \
  python3 supercomputer/run.py --backend modal --jobs research/langs/litellm/jobs.json --out runs/langs/<name> && sh supercomputer/reap.sh
```

(The job reads both variables in its command; with neither it runs upstream at the pin, v1.106.6.)

What you get, per item:

```
quota/litellm-py/team_max_budget_check: extracted in 7300 ms (reads litellm/proxy/auth/auth_checks.py: team_max_budget_check)
  checked: 2400 requests from the start, 400 from drawn states, 3 from the prover's witnesses, 4 of 4 arms
  refuted  a team whose spend has reached its max_budget is refused (40 ms): {...the request...}
  proven   a team below its max_budget is admitted (30 ms)
  proven   a team with no max_budget is admitted (25 ms)
```

- **extracted** and **checked**: the rule is your fork's code, run beside it on every request the check made; the
  arms are the branches of the code read that those requests reached.
- **proven**: the law holds for every request the rule takes (every spend, budget, session and count), not only those
  the check ran.
- **refuted**: a request where your code breaks the law, with its values. Replay it on the code to see it (the check
  already confirmed the rule and the code agree on it).
- **unknown**: neither within the search's time; raise `--ms` or read the law again.
- **refused at file:line: why**: your code left the subset there (a loop, a try/except, a call of other code the item
  doesn't answer or skip). The item's options in `specs.ts` say what it answers, skips and holds as a store; a fork that
  moves the rule into code the subset doesn't read is refused there, never approximated. Extend the options (answer
  the new call, skip a new logger) only for what you are willing to state: each is printed in the notes.
  `--bare` states none of it but each item's `needs` (the boundary inferred: a typed result read is answered, a call
  nothing reads is left out, the cache an injected store): every rule comes out byte for byte the committed one.
- **the rule and the code differ**: the extractor read your code wrong somewhere: a bug in gdp-wired, and the rule is
  not adopted. Please report it with the request it prints.

## Results at the pin (v1.106.6, 61c6ab7)

See `results.md` beside this file (the Modal run, the verdicts, and what each refutation is).
