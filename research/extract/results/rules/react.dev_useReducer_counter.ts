// Extracted by gdp-wired/extract from counter.jsx (reducer, a step function).
// Checked against the code it was read from; read again with extract() after the code changes.
import {oneOf, rule} from 'gdp-wired'

export const reducerRule = rule("reducer")
  .inputs({type: oneOf('incremented_age', '@@other')})
  .state({age: 42})
  .assume(({type}) => type.is('incremented_age'))
  .step(({age}) => ({age: age.plus(1)}))
