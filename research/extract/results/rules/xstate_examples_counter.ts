// Extracted by gdp-wired/extract from counterMachine.ts (counterMachine, an XState machine): its guards and actions read from the code.
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {int} from 'gdp-wired'
import {counterMachine} from './counterMachine'

export const counterMachineChart = fromXState(counterMachine, {context: {count: int.from(0)}, inline: {actions: new Map([[counterMachine.config.on.increment.actions, ({count}) => ({count: count.plus(1)})], [counterMachine.config.on.decrement.actions, ({count}) => ({count: count.minus(1)})]])}})
