// quota/litellm-py/virtual_key_max_budget_check: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/auth/auth_checks.py: virtual_key_max_budget_check, _apply_budget_exceeded_throttle (answered). MIT, (c) Berri AI.
// Boundary: get_current_spend (the cross-pod spend counter, litellm/proxy/proxy_server.py) answered by the request; the alert (CallInfo, asyncio.create_task) and the error message left out; whether the key is throttled instead (_apply_budget_exceeded_throttle) answered too.
// Extracted by gdp-wired/extract from auth_checks.py (virtual_key_max_budget_check, a function, each call a request).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, int, not, rule} from '../../../../core/dsl.ts'

export const virtual_key_max_budget_checkRule = rule("virtual_key_max_budget_check")
  .inputs({valid_token_max_budget: int, valid_token_max_budget_none: bool, get_current_spend: int, apply_budget_exceeded_throttle: bool})
  .state({failed: bool.from(false)})
  .step(({valid_token_max_budget_none, valid_token_max_budget, get_current_spend, apply_budget_exceeded_throttle}) => ({failed: all(not(valid_token_max_budget_none), valid_token_max_budget.atMost(get_current_spend), not(apply_budget_exceeded_throttle))}))
