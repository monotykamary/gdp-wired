# The laws of specs.ts written as a LiteLLM maintainer would: one `# gdp: law` comment above each function or method,
# over the code's own names, and the modelling choices in gdp.toml. `python3 laws.py <litellm checkout>` writes them
# into the checkout (a copy: the comments only, nothing of the code changes); then
#   npx gdp-wired check litellm/proxy/auth/auth_checks.py litellm/proxy/hooks/max_iterations_limiter.py \
#     litellm/proxy/hooks/max_budget_per_session_limiter.py litellm/router_utils/cooldown_handlers.py
import pathlib, re, shutil, sys

src = pathlib.Path(sys.argv[1])
SPEND = "get_current_spend(...)"
def budget(entity, given, mx, off=None):
    a = "an" if entity[0] in "aeiou" else "a"
    off = f" and not {off}" if off else ""
    return [
        f"{a} {entity} whose spend has reached its max_budget is refused: {given}{off} and {SPEND} >= {mx} implies failed",
        f"{a} {entity} below its max_budget is admitted: {given} and {SPEND} < {mx} implies not failed",
        f"{a} {entity} with no max_budget is admitted: not ({given}) implies not failed",
    ]
SID, CACHE = "_get_session_id(...)", "internal_usage_cache[_get_session_id(...)]"
ITER = f"{SID} is not None and _get_max_iterations(...) is not None"
SESS = f"{SID} is not None and _get_max_budget_per_session(...) is not None"
COOL = "_increment_allowed_fails(...)"
LAWS = {
    "litellm/proxy/auth/auth_checks.py": {
        "virtual_key_max_budget_check": budget("key", "valid_token.max_budget is not None", "valid_token.max_budget", "_apply_budget_exceeded_throttle(...)"),
        "team_max_budget_check": budget("team", "team_object is not None and team_object.max_budget is not None", "team_object.max_budget"),
        "_project_max_budget_check": budget("project", "project_object is not None and project_object.litellm_budget_table is not None and project_object.litellm_budget_table.max_budget is not None", "project_object.litellm_budget_table.max_budget"),
        "check_end_user_budget": budget("end user", "end_user_obj.litellm_budget_table is not None and end_user_obj.litellm_budget_table.max_budget is not None", "end_user_obj.litellm_budget_table.max_budget", "RouteChecks.is_info_route(...)"),
    },
    "litellm/proxy/hooks/max_iterations_limiter.py": {"async_pre_call_hook": [
        f"a call is admitted only while its session is below max_iterations: {ITER} and not failed implies old({CACHE}) < _get_max_iterations(...)",
        f"a session at its max_iterations is refused: {ITER} and old({CACHE}) >= _get_max_iterations(...) implies failed",
        f"every call of a limited session counts one, refused or not: {ITER} implies {CACHE} == old({CACHE}) + 1",
        f"a call with no session or no max_iterations is admitted and counts nothing: not ({ITER}) implies not failed and {CACHE} == old({CACHE})",
    ]},
    "litellm/proxy/hooks/max_budget_per_session_limiter.py": {"async_pre_call_hook": [
        f"a session whose spend has reached max_budget_per_session is refused: {SESS} and old({CACHE}) >= _get_max_budget_per_session(...) implies failed",
        f"a session below max_budget_per_session is admitted: {SESS} and old({CACHE}) < _get_max_budget_per_session(...) implies not failed",
    ]},
    "litellm/router_utils/cooldown_handlers.py": {"should_cooldown_based_on_allowed_fails_policy": [
        f"with an override, a deployment cools down exactly when its fails pass it: allowed_fails_override is not None implies not failed and result == (allowed_fails_override < {COOL})",
        f"with no override, the exception's policy governs: allowed_fails_override is None and get_allowed_fails_from_policy(...) is not None implies not failed and result == (get_allowed_fails_from_policy(...) < {COOL})",
        f"with neither, the router's allowed_fails governs: allowed_fails_override is None and get_allowed_fails_from_policy(...) is None and litellm_router_instance.allowed_fails is not None implies not failed and result == (litellm_router_instance.allowed_fails < {COOL})",
    ]},
}
for f, fns in LAWS.items():
    p = src / f
    lines = p.read_text().split("\n")
    for fn, laws in fns.items():
        i = next(k for k, l in enumerate(lines) if re.match(rf"\s*(async\s+)?def\s+{fn}\(", l))
        while i > 0 and lines[i - 1].strip().startswith("@"): i -= 1
        ind = re.match(r"\s*", lines[i]).group(0)
        lines[i:i] = [f"{ind}# gdp: law {l}" for l in laws]
    p.write_text("\n".join(lines))
shutil.copy(pathlib.Path(__file__).with_name("gdp.toml"), src / "gdp.toml")
print("laws:", sum(len(v) for fns in LAWS.values() for v in fns.values()), "comment lines in", len(LAWS), "files; gdp.toml:", sum(1 for l in open(src / "gdp.toml") if l.strip() and not l.lstrip().startswith("#")), "lines")
