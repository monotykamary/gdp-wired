// Extracted by gdp-wired/extract from cache.ts (Cache, a class).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, forall, int, Int, nat, not, oneOf, record, rule, str, when} from 'gdp-wired'

export const cacheRule = rule("Cache")
  .inputs({method: oneOf('isBlocked', 'blockUntil', 'set', 'get', 'incr'), isBlocked_identifier: str(), now: nat, blockUntil_identifier: str(), blockUntil_reset: int, set_key: str(), set_value: int, get_key: str(), incr_key: str(), incr_incrementAmount: int})
  .state({isBlocked_result_blocked: bool.from(false), isBlocked_result_reset: int.from(0), get_result: int.from(0), get_result_missing: bool.from(false), incr_result: int.from(0)})
  .maps({cache: record({has: bool, value: int}).from({has: false, value: 0})})
  .step(({method, isBlocked_identifier, now, get_key, incr_key, incr_incrementAmount, blockUntil_identifier, set_key, blockUntil_reset, set_value, cache}) => {
    const t1 = method.is('isBlocked')
    const reset = cache.at(isBlocked_identifier.id).value
    const t2 = reset.lt(now)
    const t3 = Int.of(now).atMost(reset)
    const t4 = when(t2, 0, reset)
    const t5 = method.is('blockUntil')
    const t6 = method.is('set')
    const t7 = method.is('get')
    const t8 = cache.at(get_key.id).value
    const t9 = all(cache.at(get_key.id).has, t8.eq(0).not())
    const t10 = cache.at(incr_key.id).value
    const value = when(cache.at(incr_key.id).has, t10, 0).plus(incr_incrementAmount)
    return {isBlocked_result_blocked: all(t1, cache.at(isBlocked_identifier.id).has, t3), isBlocked_result_reset: when(t1, when(cache.at(isBlocked_identifier.id).has, t4, 0), 0), get_result: when(t1, 0, when(t5, 0, when(t6, 0, when(t7, when(t9, t8, 0), 0)))), get_result_missing: all(t7, cache.at(get_key.id).has.implies(t8.eq(0))), incr_result: when(t1, 0, when(t5, 0, when(t6, 0, when(t7, 0, value)))), cache: cache.set(when(t1, isBlocked_identifier.id, when(t5, blockUntil_identifier.id, when(t6, set_key.id, incr_key.id))), {has: when(t1, all(cache.at(isBlocked_identifier.id).has, t3), any(t5, t6, not(t7), cache.at(incr_key.id).has)), value: when(t1, when(cache.at(isBlocked_identifier.id).has, t4, reset), when(t5, blockUntil_reset, when(t6, set_value, when(t7, t10, value))))})}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const cacheInvariants = [cacheRule.law("cache: a key it doesn't hold holds the defaults", ({cache}) => forall(k => any(cache.at(k).has, all(cache.at(k).value.eq(0)))))]
