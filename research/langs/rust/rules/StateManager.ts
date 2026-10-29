// circuit breaker/circuitbreaker-rs/StateManager: extracted from circuitbreaker-rs 0.1.1 (crates.io; crates.io/crates/circuitbreaker-rs), src/state.rs: StateManager::new, current, transition_from_to, trip_open, attempt_half_open, reset_closed, revert_to_open; State::from. MIT OR Apache-2.0, (c) circuitbreaker-rs authors.
// Extracted by gdp-wired/extract from state.rs (StateManager, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, nat, no, oneOf, rule, when} from '../../../../core/dsl.ts'

export const stateManagerRule = rule("StateManager")
  .params({made_at: int})
  .inputs({method: oneOf('trip_open', 'attempt_half_open', 'reset_closed', 'revert_to_open', 'current'), now: nat})
  .state({state: 0, last_transition: int.from(({made_at}) => made_at), trip_open_result: bool.from(false), attempt_half_open_result: bool.from(false), reset_closed_result: bool.from(false), revert_to_open_result: bool.from(false), current_result: oneOf('Closed', 'Open', 'HalfOpen').from('Closed'), failed: bool.from(false)})
  .step(({method, state, last_transition, now, current_result}) => {
    const t1 = method.is('trip_open')
    const t2 = state.eq(0)
    const t3 = state.eq(0).not()
    const t4 = state.eq(1)
    const t5 = all(t3, t4)
    const t6 = state.eq(1).not()
    const t7 = state.eq(2)
    const t8 = state.eq(when(any(t2, all(t6, state.eq(2).not())), 0, when(t5, 1, when(all(t3, t6, t7), 2, 0))))
    const t9 = method.is('attempt_half_open')
    const t10 = method.is('reset_closed')
    const t11 = method.is('revert_to_open')
    const t12 = when(t7, now, last_transition)
    return {state: when(t1, when(t5, state, when(t8, 1, state)), when(t9, when(t4, 2, state), when(t10, when(t7, 0, state), when(t11, when(t7, 1, state), state)))), last_transition: when(t1, when(t5, last_transition, when(t8, now, last_transition)), when(t9, when(t4, now, last_transition), when(t10, t12, when(t11, t12, last_transition)))), trip_open_result: all(t1, t3.implies(t6), t8), attempt_half_open_result: all(t9, t4), reset_closed_result: all(t10, t7), revert_to_open_result: all(t11, t7), current_result: when(t1, 'Closed', when(t9, 'Closed', when(t10, 'Closed', when(t11, 'Closed', when(method.is('current'), when(t2, 'Closed', when(t4, 'Open', when(t7, current_result.of('HalfOpen'), current_result.of('Closed')))), 'Closed'))))), failed: no}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const stateManagerInvariants = [stateManagerRule.law("state within its type's range", ({state}) => state.atMost(255).and(state.atLeast(0)))]
