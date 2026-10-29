// quota/litellm-py/check_end_user_budget: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/auth/auth_checks.py: check_end_user_budget, RouteChecks.is_info_route (answered). MIT, (c) Berri AI.
// Boundary: get_current_spend (the cross-pod spend counter, litellm/proxy/proxy_server.py) answered by the request; the alert (CallInfo, asyncio.create_task) and the error message left out; whether the route is an info route (RouteChecks.is_info_route) answered too.
// Extracted by gdp-wired/extract from auth_checks.py (check_end_user_budget, a function, each call a request).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, int, not, rule} from '../../../../core/dsl.ts'

export const check_end_user_budgetRule = rule("check_end_user_budget")
  .inputs({is_info_route: bool, end_user_obj_litellm_budget_table_none: bool, end_user_obj_litellm_budget_table_max_budget: int, end_user_obj_litellm_budget_table_max_budget_none: bool, get_current_spend: int})
  .state({failed: bool.from(false)})
  .step(({is_info_route, end_user_obj_litellm_budget_table_none, end_user_obj_litellm_budget_table_max_budget_none, end_user_obj_litellm_budget_table_max_budget, get_current_spend}) => ({failed: all(not(is_info_route), not(end_user_obj_litellm_budget_table_none), not(end_user_obj_litellm_budget_table_max_budget_none), end_user_obj_litellm_budget_table_max_budget.lt(get_current_spend))}))
