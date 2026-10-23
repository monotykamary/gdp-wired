// Extracted by gdp-wired/extract from toggleMachine.ts (toggleMachine, an XState machine): its guards and actions read from setup().
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {toggleMachine} from './toggleMachine'

export const toggleMachineChart = fromXState(toggleMachine, {})
