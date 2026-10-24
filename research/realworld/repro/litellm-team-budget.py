# Repro for quota/litellm/maxBudgetChecks#"a team whose spend has reached its max_budget is refused" and the overshoot
# law. Runs the ORIGINAL team_max_budget_check and virtual_key_max_budget_check: their source is taken verbatim from
# litellm/proxy/auth/auth_checks.py at BerriAI/litellm commit 49943cd52ea46aacf8db2e5cb2b890d580fe9bb4 (v1.106.2),
# fetched here (nothing vendored), and executed with stand-ins for what they import: get_current_spend (returns the
# counter value given), BudgetExceededError, CallInfo, the alert hook and the throttle check (off).
# Run: python3 -I research/realworld/repro/litellm-team-budget.py
import ast, asyncio, math, sys, types, urllib.request
from typing import Final

# REPRO_COMMIT=<sha> fetches another commit (the re-check of 2026-10-24 ran main e04e89c7 and v1.106.3 4fa8bf1f).
import os
URL = f"https://raw.githubusercontent.com/BerriAI/litellm/{os.environ.get('REPRO_COMMIT', '49943cd52ea46aacf8db2e5cb2b890d580fe9bb4')}/litellm/proxy/auth/auth_checks.py"
src = urllib.request.urlopen(URL).read().decode()
tree = ast.parse(src)
wanted = {"team_max_budget_check", "virtual_key_max_budget_check"}
fns = [n for n in tree.body if isinstance(n, ast.AsyncFunctionDef) and n.name in wanted]
assert {f.name for f in fns} == wanted

class BudgetExceededError(Exception):
    def __init__(self, current_cost=None, max_budget=None, message="", **kw):
        super().__init__(message); self.current_cost = current_cost; self.max_budget = max_budget

SPEND = {}
async def get_current_spend(counter_key, fallback_spend, max_budget=None, **kw):
    return SPEND.get(counter_key, fallback_spend)

litellm = types.ModuleType("litellm"); litellm.BudgetExceededError = BudgetExceededError
proxy = types.ModuleType("litellm.proxy"); ps = types.ModuleType("litellm.proxy.proxy_server"); ps.get_current_spend = get_current_spend
sys.modules.update({"litellm": litellm, "litellm.proxy": proxy, "litellm.proxy.proxy_server": ps})

class NS:
    def __init__(self, **kw): self.__dict__.update(kw)
class EntityType:
    KEY = NS(value="key"); TEAM = NS(value="team"); USER = NS(value="user")
class Logging:
    async def budget_alerts(self, **kw): return None
env = {"litellm": litellm, "math": math, "asyncio": asyncio, "Final": Final, "CallInfo": lambda **kw: NS(**kw),
       "Litellm_EntityType": EntityType, "_apply_budget_exceeded_throttle": lambda t: False, "_MASKED_KEY_NAME_RE": None,
       "UserAPIKeyAuth": object, "LiteLLM_TeamTable": object, "LiteLLM_UserTable": object, "ProxyLogging": object}
exec(compile(ast.Module(body=fns, type_ignores=[]), URL, "exec"), env)

async def outcome(check, *args):
    try:
        await check(*args); return "admitted"
    except BudgetExceededError as e:
        return f"refused ({e})"

async def main():
    token = NS(token="k", max_budget=1.0, spend=0.0, soft_budget=None, user_id=None, team_id="t", org_id=None, key_alias=None, key_name=None, team_alias=None)
    team = NS(team_id="t", max_budget=1.0, spend=0.0)
    # Spend exactly at max_budget: the key is refused, the team is not (the counterexample: teamMax 0, teamSpend 0).
    SPEND.update({"spend:key:k": 1.0, "spend:team:t": 1.0})
    print("key  at max_budget:", await outcome(env["virtual_key_max_budget_check"], token, Logging(), None))
    print("team at max_budget:", await outcome(env["team_max_budget_check"], team, token, Logging()))
    # Overlap: two requests read the counter before either response's cost is added; both are admitted.
    SPEND.update({"spend:key:k": 0.9})
    first = await outcome(env["virtual_key_max_budget_check"], token, Logging(), None)
    second = await outcome(env["virtual_key_max_budget_check"], token, Logging(), None)
    SPEND["spend:key:k"] += 0.5 + 0.5  # increment_spend_counters for both responses (cost 0.5 each)
    print(f"two overlapping requests at spend 0.9 of 1.0: {first}, {second}; spend after both: {SPEND['spend:key:k']:.1f} (max_budget + one cost = 1.5)")

asyncio.run(main())
