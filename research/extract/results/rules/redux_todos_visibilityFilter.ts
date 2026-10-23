// Extracted by gdp-wired/extract from visibilityFilter.js (default, a step function).
// Checked against the code it was read from; read again with extract() after the code changes.
import {oneOf, rule, str, when} from 'gdp-wired'

export const visibilityFilterRule = rule("visibilityFilter")
  .inputs({type: oneOf('SET_VISIBILITY_FILTER', '@@other'), filter: str()})
  .state({state: str().from('SHOW_ALL')})
  .step(({type, filter, state}) => ({state: when(type.is('SET_VISIBILITY_FILTER'), filter, state)}))
