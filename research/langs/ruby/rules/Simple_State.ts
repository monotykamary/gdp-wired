// circuit breaker/semian/Simple::State: extracted from semian 0.28.4 (rubygems.org; Shopify/semian), lib/semian/simple_state.rb: Semian::Simple::State#open!, close!, half_open!, reset, open?, closed?, half_open?. MIT, (c) Shopify.
// Extracted by gdp-wired/extract from simple_state.rb (State, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, oneOf, rule, when} from '../../../../core/dsl.ts'

export const stateRule = rule("State")
  .inputs({method: oneOf('open!', 'close!', 'half_open!', 'reset', 'open?', 'closed?', 'half_open?')})
  .state({value: oneOf('open', 'closed', 'half_open').from('closed'), open_result: oneOf('open', 'closed', 'half_open').from('open'), close_result: oneOf('open', 'closed', 'half_open').from('open'), half_open_result: oneOf('open', 'closed', 'half_open').from('open'), reset_result: oneOf('open', 'closed', 'half_open').from('open'), open_p_result: bool.from(false), closed_p_result: bool.from(false), half_open_p_result: bool.from(false)})
  .step(({method, value}) => {
    const t1 = method.is('open!')
    const t2 = method.is('close!')
    const t3 = method.is('half_open!')
    const t4 = method.is('reset')
    return {value: when(t1, 'open', when(t2, 'closed', when(t3, 'half_open', when(t4, 'closed', value)))), open_result: 'open', close_result: when(t1, 'open', when(t2, value.of('closed'), value.of('open'))), half_open_result: when(t1, 'open', when(t2, 'open', when(t3, value.of('half_open'), value.of('open')))), reset_result: when(t1, 'open', when(t2, 'open', when(t3, 'open', when(t4, value.of('closed'), value.of('open'))))), open_p_result: all(method.is('open?'), value.is('open')), closed_p_result: all(method.is('closed?'), value.is('closed')), half_open_p_result: all(method.is('half_open?'), value.is('half_open'))}
  })
