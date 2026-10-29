# Results at the pin

LiteLLM v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b, the latest release), Modal, 2 vCPU, one job
(`research/langs/litellm/jobs.json`: the checkout, `uv pip install -e '.[proxy]'`, `run.ts --ms 60000 --write`), 252 s
of which the install is most; `runs/langs/modal/run3`, and again on gen/rust's executor in `runs/langs/modal/run4` (the same verdicts; MaxIterationsHandler's rule printed with one more hoisted condition). `results.json` beside this file is the run's own output.

**7 of 7 items extracted and checked, 21 laws: 19 proven, 2 refuted, none unknown.**

| Item | Checked (requests from the start / drawn states / witnesses, arms) | Laws |
| --- | --- | --- |
| `virtual_key_max_budget_check` | 2,221 / 400 / 0, 5 of 5 | 3 proven |
| `team_max_budget_check` | 2,308 / 400 / 0, 4 of 4 | 2 proven, **1 refuted** |
| `_project_max_budget_check` | 2,287 / 400 / 0, 6 of 6 | 3 proven |
| `check_end_user_budget` | 2,287 / 400 / 0, 5 of 5 | 2 proven, **1 refuted** |
| `MaxIterationsHandler` | 2,337 / 400 / 4, 9 of 9 | 4 proven |
| `MaxBudgetPerSessionHandler` | 2,400 / 400 / 0, 8 of 8 | 2 proven |
| `should_cooldown_based_on_allowed_fails_policy` | 2,049 / 400 / 4, 1 of 1 | 3 proven |

Every law takes under 0.4 s. Extraction and the check take 5 to 18 s an item, most of it importing LiteLLM's proxy.

**The two refutations** are one inconsistency, LiteLLM's own `tests/e2e/quota_management/budgets/BUDGET_CODE_MATRIX.md`
names it ("Comparison operators are inconsistent: key/user use `>=`, team/end-user main budget use `>`"): a team, and an
end user, whose spend equals the max_budget are admitted, where a key, a project, a user and an org are refused. The
prover's request is the smallest: max_budget 0, spend 0. The hand-written item (research/realworld/items/
quotaflag-quota.ts, v1.106.2) found the team's; the extraction finds it again at v1.106.6 from the code itself, and the
end user's beside it. Triage in research/realworld/triage/litellm-py.json. Nothing was reported.

**What was read, and what was stated** (each extraction's notes say it in full):

- The four budget checks are read whole, but for the spend counter (`get_current_spend`, Redis then the DB: other code,
  answered by the request), the alert (`CallInfo`, `asyncio.create_task(budget_alerts(...))`) and the error message
  (`_MASKED_KEY_NAME_RE`), left out: the check runs them as they are. The key's over-budget throttle
  (`_apply_budget_exceeded_throttle`, reading two settings) is answered, and its law says "unless throttled".
- The two session hooks are read with the proxy's internal usage cache stated as a store with Redis off: the in-memory
  path every limiter falls back to (`dual_cache.redis_cache` None). The counter's TTL is left out (the store keeps what
  is set). The session id and the limit (`_get_session_id`, `_get_max_iterations`, `_get_max_budget_per_session`:
  request metadata and the agent registry) are answered. The per-session budget's success event, which adds a
  response's cost, keys the cache by the raw key string, which the store can't relate to the f-string template; only
  the pre-call check is read, and its laws hold for every spend the cache may hold.
- The cooldown policy is read whole but for the fail counter (`_increment_allowed_fails`, `DualCache.increment_cache`)
  and the router's per-exception policy (`Router.get_allowed_fails_from_policy`), answered.

**Not read, and why** (the next targets, each a construct the subset refuses today):

- `parallel_request_limiter_v3.py`'s `_atomic_check_and_increment_in_memory` (the RPM/TPM windows): loops over the
  request's descriptors, a dict comprehension, a store of mixed values (window starts as strings, counters as ints).
  Needs a loop over a request's list unrolled to a stated length, and a store with a sort per template.
- `_is_cooldown_required`: a loop over a constant list and `try/except` around an `int()` parse.
- `InMemoryCache` (`caching/in_memory_cache.py`): its eviction loops over a heap.
- `budget_manager.py`'s `BudgetManager`: nested dicts (a user's per-model costs), and threads saving to a file.
