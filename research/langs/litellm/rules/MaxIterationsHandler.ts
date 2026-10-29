// rate limit/litellm-py/MaxIterationsHandler: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/proxy/hooks/max_iterations_limiter.py: _PROXY_MaxIterationsHandler.__init__, async_pre_call_hook, _make_cache_key, _increment_and_get, _in_memory_increment (_get_session_id and _get_max_iterations answered). MIT, (c) Berri AI.
// Boundary: the session counter in the internal usage cache, Redis off (its Lua INCR path not read), its TTL left out; the session id and max_iterations answered by the request.
// Extracted by gdp-wired/extract from max_iterations_limiter.py (_PROXY_MaxIterationsHandler, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, forall, int, nat, not, record, rule, str, when} from '../../../../core/dsl.ts'

export const _PROXY_MaxIterationsHandlerRule = rule("_PROXY_MaxIterationsHandler")
  .inputs({get_session_id: str(), get_session_id_none: bool, get_max_iterations: int, get_max_iterations_none: bool})
  .state({failed: bool.from(false)})
  .maps({internal_usage_cache_session_iterations_count: record({has: bool, value: nat}).from({has: false, value: 0})})
  .step(({get_session_id_none, get_max_iterations_none, get_max_iterations, get_session_id, internal_usage_cache_session_iterations_count}) => {
    const t1 = not(get_max_iterations_none)
    const t2 = internal_usage_cache_session_iterations_count.at(get_session_id.id).value
    const t3 = when(internal_usage_cache_session_iterations_count.at(get_session_id.id).has, t2, 0).plus(1)
    return {failed: all(not(get_session_id_none), t1, get_max_iterations.lt(t3)), internal_usage_cache_session_iterations_count: internal_usage_cache_session_iterations_count.set(get_session_id.id, {has: when(get_session_id_none, internal_usage_cache_session_iterations_count.at(get_session_id.id).has, any(t1, internal_usage_cache_session_iterations_count.at(get_session_id.id).has)), value: when(get_session_id_none, t2, when(get_max_iterations_none, t2, t3))})}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const _PROXY_MaxIterationsHandlerInvariants = [_PROXY_MaxIterationsHandlerRule.law("internal_usage_cache_session_iterations_count: a key it doesn't hold holds the defaults", ({internal_usage_cache_session_iterations_count}) => forall(k => any(internal_usage_cache_session_iterations_count.at(k).has, all(internal_usage_cache_session_iterations_count.at(k).value.eq(0)))))]
