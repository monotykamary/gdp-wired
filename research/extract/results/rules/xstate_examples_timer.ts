// Extracted by gdp-wired/extract from timerMachine.ts (timerMachine, an XState machine): its guards and actions read from the code.
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {int} from 'gdp-wired'
import {timerMachine} from './timerMachine'

export const timerMachineChart = fromXState(timerMachine, {context: {seconds: int.from(0)}, inline: {guards: new Map([[timerMachine.config.states.stopped.on.start.guard, ({seconds}) => seconds.gt(0)], [timerMachine.config.states.running.always.guard, ({seconds}) => seconds.eq(0)], [timerMachine.config.on.reset.guard, ({seconds}) => seconds.gt(0)]]), actions: new Map([[timerMachine.config.states.stopped.on.minute.actions, ({seconds}) => ({seconds: seconds.plus(60)})], [timerMachine.config.states.stopped.on.second.actions, ({seconds}) => ({seconds: seconds.plus(1)})], [timerMachine.config.states.running.on.TICK.actions, ({seconds}) => ({seconds: seconds.minus(1)})], [timerMachine.config.on.reset.actions, () => ({seconds: 0})]])}})
