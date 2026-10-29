// circuit breaker/ex_break/Breaker: extracted from ex_break 0.0.9 (hex.pm; jclem/ex_break), lib/ex_break/breaker.ex: ExBreak.Breaker.increment, is_tripped, reset_tripped (an Agent over the breaker struct). MIT, (c) Jonathan Clem.
// Extracted by gdp-wired/extract from breaker.ex (Breaker, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, Int, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const breakerRule = rule("Breaker")
  .inputs({method: oneOf('increment', 'is_tripped', 'reset_tripped'), increment_threshold: int, now: nat, is_tripped_timeout_sec: int})
  .state({break_count: 0, tripped: bool.from(false), tripped_at: 0, tripped_at_none: bool.from(true), is_tripped_result: bool.from(false)})
  .assume(({method, tripped, tripped_at_none}) => not(all(method.is('is_tripped'), tripped, tripped_at_none)))
  .step(({method, break_count, tripped, increment_threshold, now, tripped_at_none, tripped_at, is_tripped_timeout_sec}) => {
    const t1 = method.is('increment')
    const t2 = break_count.plus(1)
    const t3 = method.is('is_tripped')
    const t4 = increment_threshold.atMost(t2)
    const t5 = all(not(tripped), not(tripped_at_none))
    return {break_count: when(t1, t2, when(t3, break_count, when(tripped, 0, break_count))), tripped: when(t1, t4, all(t3, tripped)), tripped_at: when(t1, when(t4, now, 0), when(t3, when(tripped_at_none, 0, tripped_at), when(t5, tripped_at, 0))), tripped_at_none: when(t1, Int.of(t2).lt(increment_threshold), when(t3, tripped_at_none, not(tripped).implies(tripped_at_none))), is_tripped_result: all(t3, tripped, Int.of(now).minus(tripped_at).lt(is_tripped_timeout_sec))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const breakerInvariants = [breakerRule.law("tripped_at: a None one holds 0", ({tripped_at, tripped_at_none}) => any(tripped_at_none.not(), tripped_at.eq(0)))]
