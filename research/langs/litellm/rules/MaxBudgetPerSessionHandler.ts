// quota/litellm-py/MaxBudgetPerSessionHandler: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/hooks/max_budget_per_session_limiter.py: _PROXY_MaxBudgetPerSessionHandler.__init__, async_pre_call_hook, _make_cache_key, _get_current_spend (_get_session_id and _get_max_budget_per_session answered). MIT, (c) Berri AI.
// Boundary: the session's spend in the internal usage cache, Redis off, read only (the success event that adds a response's cost keys it by the raw key, not read here: the claim is for every spend the cache may hold); the session id and the budget answered by the request.
// Extracted by gdp-wired/extract from max_budget_per_session_limiter.py (_PROXY_MaxBudgetPerSessionHandler, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, forall, int, nat, not, record, rule, str, when} from '../../../../core/dsl.ts'

export const _PROXY_MaxBudgetPerSessionHandlerRule = rule("_PROXY_MaxBudgetPerSessionHandler")
  .inputs({get_max_budget_per_session: int, get_max_budget_per_session_none: bool, get_session_id: str(), get_session_id_none: bool})
  .state({failed: bool.from(false)})
  .maps({internal_usage_cache_session_budget_spend: record({has: bool, value: nat}).from({has: false, value: 0})})
  .step(({get_max_budget_per_session_none, get_session_id_none, get_max_budget_per_session, get_session_id, internal_usage_cache_session_budget_spend}) => ({failed: all(not(get_max_budget_per_session_none), not(get_session_id_none), get_max_budget_per_session.atMost(when(internal_usage_cache_session_budget_spend.at(get_session_id.id).has, internal_usage_cache_session_budget_spend.at(get_session_id.id).value, 0)))}))

// What every state of the code is: a law about every state is about the code's with these beside it.
export const _PROXY_MaxBudgetPerSessionHandlerInvariants = [_PROXY_MaxBudgetPerSessionHandlerRule.law("internal_usage_cache_session_budget_spend: a key it doesn't hold holds the defaults", ({internal_usage_cache_session_budget_spend}) => forall(k => any(internal_usage_cache_session_budget_spend.at(k).has, all(internal_usage_cache_session_budget_spend.at(k).value.eq(0)))))]
