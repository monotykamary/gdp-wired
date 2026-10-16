// The three compared rules as one examples domain, so lean-kernel/export-kernel.ts --examples ../compare/domain.ts sends
// their kernel trees to the Lean twin (compare/twin.ts), and examples/harness.ts can run them like any other domain.
import {type Domain, machineCase} from '../examples/harness.ts'
import {bounded, budget} from './gdpwired/budget.ts'
import {capLaws, caps} from './gdpwired/caps.ts'
import {ceiling, proved} from './gdpwired/window.ts'

export const domain: Domain = {
  domain: 'compare',
  about: 'the budget, per-key caps and sliding-window rules of compare/',
  cases: [
    machineCase('budget', 'spend stays within b + m', budget, [bounded]),
    machineCase('caps', 'grants per account <= 1 and per day <= d, at every key', caps, capLaws),
    machineCase('window', 'admitted requests in the window ending at now <= c', proved, [ceiling]),
  ],
}
