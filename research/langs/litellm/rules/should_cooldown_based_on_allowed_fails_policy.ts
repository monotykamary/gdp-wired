// circuit breaker/litellm-py/should_cooldown_based_on_allowed_fails_policy: extracted from BerriAI/litellm v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), litellm/router_utils/cooldown_handlers.py: should_cooldown_based_on_allowed_fails_policy (Router.get_allowed_fails_from_policy and _increment_allowed_fails answered). MIT, (c) Berri AI.
// Boundary: the fleet-wide fail counter (_increment_allowed_fails: DualCache.increment_cache, Redis or this worker) and the router's per-exception policy (Router.get_allowed_fails_from_policy) answered by the request; the counter's key and TTL not read.
// Extracted by gdp-wired/extract from cooldown_handlers.py (should_cooldown_based_on_allowed_fails_policy, a function, each call a request).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, not, rule, when} from '../../../../core/dsl.ts'

export const should_cooldown_based_on_allowed_fails_policyRule = rule("should_cooldown_based_on_allowed_fails_policy")
  .inputs({allowed_fails_override: int, allowed_fails_override_none: bool, get_allowed_fails_from_policy: int, get_allowed_fails_from_policy_none: bool, litellm_router_instance_allowed_fails: int, litellm_router_instance_allowed_fails_none: bool, increment_allowed_fails: int})
  .state({should_cooldown_based_on_allowed_fails_policy_result: bool.from(false), failed: bool.from(false)})
  .step(({allowed_fails_override_none, get_allowed_fails_from_policy_none, litellm_router_instance_allowed_fails_none, litellm_router_instance_allowed_fails, get_allowed_fails_from_policy, allowed_fails_override, increment_allowed_fails}) => {
    const t1 = any(not(allowed_fails_override_none), not(get_allowed_fails_from_policy_none), not(litellm_router_instance_allowed_fails_none))
    return {should_cooldown_based_on_allowed_fails_policy_result: all(t1, when(allowed_fails_override_none, when(get_allowed_fails_from_policy_none, litellm_router_instance_allowed_fails, get_allowed_fails_from_policy), allowed_fails_override).lt(increment_allowed_fails)), failed: all(allowed_fails_override_none, get_allowed_fails_from_policy_none, litellm_router_instance_allowed_fails_none)}
  })
