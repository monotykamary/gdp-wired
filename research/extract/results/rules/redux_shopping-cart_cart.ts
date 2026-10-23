// Extracted by gdp-wired/extract from cart.js (quantityById, a step function).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, forall, nat, oneOf, record, rule, when} from 'gdp-wired'

export const quantityByIdRule = rule("quantityById")
  .inputs({type: oneOf('ADD_TO_CART', '@@other'), productId: nat})
  .maps({state: record({has: bool, value: nat}).from({has: false, value: 0})})
  .step(({type, productId, state}) => {
    const t1 = type.is('ADD_TO_CART')
    const t2 = state.at(productId).value
    return {state: state.set(productId, {has: any(t1, state.at(productId).has), value: when(t1, when(all(state.at(productId).has, t2.eq(0).not()), t2, 0).plus(1), t2)})}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const quantityByIdInvariants = [quantityByIdRule.law("state: a key it doesn't hold holds the defaults", ({state}) => forall(k => any(state.at(k).has, all(state.at(k).value.eq(0)))))]
