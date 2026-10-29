// circuit breaker/semian/Simple::Integer: extracted from semian 0.28.4 (rubygems.org; Shopify/semian), lib/semian/simple_integer.rb: Semian::Simple::Integer#increment, reset. MIT, (c) Shopify.
// Extracted by gdp-wired/extract from simple_integer.rb (Integer, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {int, oneOf, rule, when} from '../../../../core/dsl.ts'

export const integerRule = rule("Integer")
  .inputs({method: oneOf('increment', 'reset'), increment_val: int})
  .state({value: int.from(0), increment_result: int.from(0), reset_result: 0})
  .step(({method, value, increment_val}) => {
    const t1 = when(method.is('increment'), value.plus(increment_val), 0)
    return {value: t1, increment_result: t1, reset_result: 0}
  })
