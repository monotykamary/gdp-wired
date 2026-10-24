// Extracted by gdp-wired/extract from websocket.machine.ts (websocketMachine, an XState machine): its guards and actions read from the code.
// Checked against XState's own actor; read again with extractXState() after the code changes.
import {fromXState} from 'gdp-wired/xstate'
import {websocketMachine} from './websocket.machine'

export const websocketMachineChart = fromXState(websocketMachine, {ignore: ["id","yDoc","onSync","token"], events: ["OPEN","xstate.after(retry_delay)#websocketMachine.retry","done.invoke.authenticate","error.platform.authenticate","connection.error","CLOSE","RECONNECT","RETRY","connection.ready"], guards: {"underRetryLimit": ({retries, retryLimit}) => retries.lt(retryLimit)}, actions: {"assignDataToContext": null, "assignTokenToContext": null, "incrementRetries": ({retries}) => ({retries: retries.plus(1)})}})
