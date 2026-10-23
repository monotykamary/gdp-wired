// Extracted by gdp-wired/extract from counterSlice.ts (counterSlice, a step function).
// Checked against the code it was read from; read again with extract() after the code changes.
import {int, oneOf, rule, when} from 'gdp-wired'

export const counterSliceRule = rule("counterSlice")
  .inputs({type: oneOf('counter/increment', 'counter/decrement', 'counter/incrementByAmount', 'counter/fetchCount/pending', 'counter/fetchCount/fulfilled', 'counter/fetchCount/rejected', '@@other'), payload: int})
  .state({value: int.from(0), status: oneOf('idle', 'loading', 'failed').from('idle')})
  .step(({type, value, payload, status}) => {
    const t1 = type.is('counter/increment')
    const t2 = type.is('counter/decrement')
    const t3 = type.is('counter/incrementByAmount')
    const t4 = value.plus(payload)
    const t5 = type.is('counter/fetchCount/pending')
    const t6 = type.is('counter/fetchCount/fulfilled')
    return {value: when(t1, value.plus(1), when(t2, value.minus(1), when(t3, t4, when(t5, value, when(t6, t4, value))))), status: when(t1, status, when(t2, status, when(t3, status, when(t5, 'loading', when(t6, 'idle', when(type.is('counter/fetchCount/rejected'), 'failed', status))))))}
  })
