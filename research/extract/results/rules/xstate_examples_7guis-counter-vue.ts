// Extracted by gdp-wired/extract from counterMachine.ts (counterMachine, an XState machine): its guards and actions read from setup().
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {counterMachine} from './counterMachine'

export const counterMachineChart = fromXState(counterMachine, {inline: {actions: new Map([[counterMachine.config.states.ready.on.increase.actions, ({count}) => ({count: count.plus(1)})]])}})
