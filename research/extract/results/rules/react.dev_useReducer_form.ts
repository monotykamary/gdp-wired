// Extracted by gdp-wired/extract from form.jsx (reducer, a step function).
// Checked against the code it was read from; read again with extract() after the code changes.
import {any, oneOf, rule, str, when} from 'gdp-wired'

export const reducerRule = rule("reducer")
  .inputs({type: oneOf('incremented_age', 'changed_name', '@@other'), nextName: str()})
  .state({name: str().from('Taylor'), age: 42})
  .assume(({type}) => any(type.is('incremented_age'), type.is('changed_name')))
  .step(({type, name, nextName, age}) => {
    const t1 = type.is('incremented_age')
    return {name: when(t1, name, nextName), age: when(t1, age.plus(1), age)}
  })
