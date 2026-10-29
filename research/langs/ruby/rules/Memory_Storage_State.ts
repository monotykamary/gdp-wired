// circuit breaker/stoplight/Memory::Storage::State: extracted from stoplight 6.0.0 (rubygems.org; bolshakov/stoplight), lib/stoplight/infrastructure/memory/storage/state.rb: Stoplight::Infrastructure::Memory::Storage::State#transition_to_color, clear (and transition_to_green, _yellow, _red). MIT, (c) Cameron Desautels, Taylor Fausak, Tëma Bolshakov.
// Extracted by gdp-wired/extract from state.rb (State, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, Int, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const stateRule = rule("State")
  .params({cool_off_time: int})
  .inputs({method: oneOf('transition_to_color', 'clear'), transition_to_color_color: oneOf('green', 'yellow', 'red'), now: nat})
  .state({locked_state: oneOf('unlocked').from('unlocked'), cool_off_time_: int.from(({cool_off_time}) => cool_off_time), recovered_at: 0, recovered_at_none: bool.from(true), recovery_scheduled_after: int.from(0), recovery_scheduled_after_none: bool.from(true), breached_at: 0, breached_at_none: bool.from(true), recovery_started_at: 0, recovery_started_at_none: bool.from(true), transition_to_color_result: bool.from(false)})
  .assume(({method, transition_to_color_color}) => not(all(method.is('transition_to_color'), not(transition_to_color_color.is('green')), not(transition_to_color_color.is('yellow')), not(transition_to_color_color.is('red')))))
  .step(({method, locked_state, transition_to_color_color, recovered_at_none, now, recovered_at, recovery_scheduled_after_none, recovery_scheduled_after, cool_off_time_, breached_at_none, breached_at, recovery_started_at_none, recovery_started_at}) => {
    const t1 = method.is('transition_to_color')
    const t2 = transition_to_color_color.is('green')
    const t3 = not(t1)
    const t4 = transition_to_color_color.is('yellow')
    const t5 = not(t4)
    const t6 = when(t2, all(not(recovered_at_none), not(recovery_scheduled_after_none)), t5)
    const t7 = when(t2, all(not(recovered_at_none), not(breached_at_none)), t5)
    const t8 = when(t2, all(not(recovered_at_none), not(recovery_started_at_none)), t4)
    return {locked_state: when(t1, locked_state, 'unlocked'), recovered_at: when(t1, when(t2, when(recovered_at_none, now, recovered_at), 0), 0), recovered_at_none: any(t3, not(t2)), recovery_scheduled_after: when(t1, when(t6, when(t2, recovery_scheduled_after, Int.of(now).plus(cool_off_time_)), 0), 0), recovery_scheduled_after_none: any(t3, not(t6)), breached_at: when(t1, when(t7, when(t2, breached_at, when(breached_at_none, now, breached_at)), 0), 0), breached_at_none: any(t3, not(t7)), recovery_started_at: when(t1, when(t8, when(t2, recovery_started_at, when(recovery_started_at_none, now, recovery_started_at)), 0), 0), recovery_started_at_none: any(t3, not(t8)), transition_to_color_result: all(t1, when(t2, recovered_at_none, when(t4, recovery_started_at_none, breached_at_none)))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const stateInvariants = [stateRule.law("recovered_at: a None one holds 0", ({recovered_at, recovered_at_none}) => any(recovered_at_none.not(), recovered_at.eq(0))), stateRule.law("recovery_scheduled_after: a None one holds 0", ({recovery_scheduled_after, recovery_scheduled_after_none}) => any(recovery_scheduled_after_none.not(), recovery_scheduled_after.eq(0))), stateRule.law("breached_at: a None one holds 0", ({breached_at, breached_at_none}) => any(breached_at_none.not(), breached_at.eq(0))), stateRule.law("recovery_started_at: a None one holds 0", ({recovery_started_at, recovery_started_at_none}) => any(recovery_started_at_none.not(), recovery_started_at.eq(0)))]
