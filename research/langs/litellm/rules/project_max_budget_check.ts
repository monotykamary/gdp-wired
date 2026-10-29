// quota/litellm-py/_project_max_budget_check: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/auth/auth_checks.py: _project_max_budget_check. MIT, (c) Berri AI.
// Boundary: get_current_spend (the cross-pod spend counter, litellm/proxy/proxy_server.py) answered by the request; the alert (CallInfo, asyncio.create_task) and the error message left out.
// Extracted by gdp-wired/extract from auth_checks.py (_project_max_budget_check, a function, each call a request).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, not, rule} from '../../../../core/dsl.ts'

export const _project_max_budget_checkRule = rule("_project_max_budget_check")
  .inputs({project_object_none: bool, project_object_litellm_budget_table_none: bool, project_object_litellm_budget_table_max_budget: int, project_object_litellm_budget_table_max_budget_none: bool, get_current_spend: int})
  .state({failed: bool.from(false)})
  .step(({project_object_none, project_object_litellm_budget_table_none, project_object_litellm_budget_table_max_budget_none, project_object_litellm_budget_table_max_budget, get_current_spend}) => {
    const t1 = not(project_object_litellm_budget_table_none)
    const t2 = not(project_object_litellm_budget_table_max_budget_none)
    return {failed: any(all(not(project_object_none), t1, t2, t1.implies(project_object_litellm_budget_table_max_budget_none)), all(not(project_object_none), t1, t2, project_object_litellm_budget_table_max_budget.atMost(get_current_spend)))}
  })
