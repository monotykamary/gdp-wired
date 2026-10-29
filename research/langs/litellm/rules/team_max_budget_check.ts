// quota/litellm-py/team_max_budget_check: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/auth/auth_checks.py: team_max_budget_check. MIT, (c) Berri AI.
// Boundary: get_current_spend (the cross-pod spend counter, litellm/proxy/proxy_server.py) answered by the request; the alert (CallInfo, asyncio.create_task) and the error message left out.
// Extracted by gdp-wired/extract from auth_checks.py (team_max_budget_check, a function, each call a request).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, int, not, rule} from '../../../../core/dsl.ts'

export const team_max_budget_checkRule = rule("team_max_budget_check")
  .inputs({team_object_none: bool, team_object_max_budget: int, team_object_max_budget_none: bool, get_current_spend: int})
  .state({failed: bool.from(false)})
  .step(({team_object_none, team_object_max_budget_none, team_object_max_budget, get_current_spend}) => ({failed: all(not(team_object_none), not(team_object_max_budget_none), team_object_max_budget.lt(get_current_spend))}))
