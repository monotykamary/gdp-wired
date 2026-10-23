// Extracted by gdp-wired/extract from machine.ts (machine, an XState machine): its guards and actions read from setup().
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {machine} from './machine'

export const machineChart = fromXState(machine, {inline: {actions: new Map([[machine.config.states.red.on.TIMER.actions, ({cycles}) => ({cycles: cycles.plus(1)})]])}})
