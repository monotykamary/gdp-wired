// state machine/PX4/Hysteresis: extracted from PX4-Autopilot 1.17.0 (PX4/PX4-Autopilot), src/lib/hysteresis/hysteresis.cpp and .h: systemlib::Hysteresis (its constructor, get_state, set_hysteresis_time_from, set_state_and_update, update; drivers/drv_hrt.h stood in for: hrt_abstime as uint64_t). BSD-3-Clause, (c) PX4 Development Team.
// Extracted by gdp-wired/extract from Hysteresis.cpp (Hysteresis, a class).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const hysteresisRule = rule("Hysteresis")
  .params({init_state: bool})
  .inputs({method: oneOf('get_state', 'set_hysteresis_time_from', 'set_state_and_update', 'update'), set_hysteresis_time_from_from_state: bool, set_hysteresis_time_from_new_hysteresis_time_us: nat, set_state_and_update_new_state: bool, set_state_and_update_now_us: nat, update_now_us: nat})
  .state({last_time_to_change_state: 0, time_from_true_us: 0, time_from_false_us: 0, state: bool.from(({init_state}) => init_state), requested_state: bool.from(({init_state}) => init_state), get_state_result: bool.from(false)})
  .assume(({method, set_hysteresis_time_from_new_hysteresis_time_us, set_state_and_update_now_us, update_now_us}) => all(method.is('set_hysteresis_time_from').implies(set_hysteresis_time_from_new_hysteresis_time_us.atLeast(0)), method.is('set_state_and_update').implies(set_state_and_update_now_us.atLeast(0)), method.is('update').implies(update_now_us.atLeast(0))))
  .step(({method, last_time_to_change_state, set_state_and_update_new_state, state, requested_state, set_state_and_update_now_us, time_from_true_us, set_hysteresis_time_from_from_state, set_hysteresis_time_from_new_hysteresis_time_us, time_from_false_us, update_now_us}) => {
    const t1 = method.is('get_state')
    const t2 = method.is('set_hysteresis_time_from')
    const t3 = method.is('set_state_and_update')
    const t4 = when(set_state_and_update_new_state, 1, 0)
    const t5 = when(state, 1, 0)
    const t6 = t4.eq(t5)
    const t7 = when(requested_state, 1, 0)
    const t8 = t4.eq(t7)
    const t9 = when(t6, last_time_to_change_state, when(t8, last_time_to_change_state, set_state_and_update_now_us))
    const t10 = when(t4.eq(t5).not(), when(t4.eq(t7).not(), set_state_and_update_new_state, requested_state), state)
    return {last_time_to_change_state: when(t1, last_time_to_change_state, when(t2, last_time_to_change_state, when(t3, t9, last_time_to_change_state))), time_from_true_us: when(t1, time_from_true_us, when(t2, when(set_hysteresis_time_from_from_state, set_hysteresis_time_from_new_hysteresis_time_us, time_from_true_us), time_from_true_us)), time_from_false_us: when(t1, time_from_false_us, when(t2, when(set_hysteresis_time_from_from_state, time_from_false_us, set_hysteresis_time_from_new_hysteresis_time_us), time_from_false_us)), state: when(t1, state, when(t2, state, when(t3, when(when(t10, 1, 0).eq(t5).not(), when(all(state, not(t10)), all(set_state_and_update_now_us.lt(t9.plus(time_from_true_us)), state), when(all(not(state), t10), any(t9.plus(time_from_false_us).atMost(set_state_and_update_now_us), state), state)), state), when(t7.eq(t5).not(), when(all(state, not(requested_state)), all(update_now_us.lt(last_time_to_change_state.plus(time_from_true_us)), state), when(all(not(state), requested_state), any(last_time_to_change_state.plus(time_from_false_us).atMost(update_now_us), state), state)), state)))), requested_state: when(t1, requested_state, when(t2, requested_state, when(t3, t10, requested_state))), get_state_result: all(t1, state)}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const hysteresisInvariants = [hysteresisRule.law("last_time_to_change_state within its type's range", ({last_time_to_change_state}) => last_time_to_change_state.atLeast(0)), hysteresisRule.law("time_from_true_us within its type's range", ({time_from_true_us}) => time_from_true_us.atLeast(0)), hysteresisRule.law("time_from_false_us within its type's range", ({time_from_false_us}) => time_from_false_us.atLeast(0))]
