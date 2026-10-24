// Extracted by gdp-wired/extract from stopwatchMachine.ts (stopwatchMachine, an XState machine): its guards and actions read from the code.
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {stopwatchMachine} from './stopwatchMachine'

export const stopwatchMachineChart = fromXState(stopwatchMachine, {inline: {actions: new Map([[stopwatchMachine.config.states.running.on.TICK.actions, ({elapsed}) => ({elapsed: elapsed.plus(1)})], [stopwatchMachine.config.on.reset.actions, () => ({elapsed: 0})]])}})
