// Extracted by gdp-wired/extract from uploader-machine.ts (createUploaderMachine, a function that makes an XState machine): its guards and actions read from the code.
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {bool} from 'gdp-wired'
import {createUploaderMachine} from './uploader-machine'

// The machine's states and transitions are the same whatever it is given (the functions are its inputs, the context its params).
const machine = createUploaderMachine({} as never)
export const createUploaderMachineChart = fromXState(machine, {inputs: {abortRequested: bool}, guards: {"abortRequested": ({abortRequested}) => abortRequested}, actions: {"killTransport": null, "recordFailure": null}})
