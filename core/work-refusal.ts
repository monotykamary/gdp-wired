// Diagnostic only: never changes refusal ownership, admission or counters.
import {workLedger} from './work-admission.ts'
export function workRefusalWhy(error:Error):string {
 const refusal=workLedger.capacityRefusal(error)
 return refusal?`${error.message} [limits=${[...new Set(refusal.limiting.map(endpoint=>endpoint.kind))].join(',')}]`:error.message
}
