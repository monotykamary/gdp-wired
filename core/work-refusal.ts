// Diagnostic only: never changes refusal ownership, admission or counters.
import {workLedger} from './work-admission.ts'
import {type SearchContext} from './search-termination.ts'
// Non-authoritative context captured before a search unwinds its SAT/model state.
// Keep the error identity and the ledger's authenticated refusal untouched.
const contexts = new WeakMap<Error, SearchContext>()
export function captureWorkContext(error: Error, context: SearchContext): void {
 if (!contexts.has(error)) contexts.set(error, context)
}
export const workContext = (error: Error): SearchContext | undefined => contexts.get(error)
export function workRefusalWhy(error:Error):string {
 const refusal=workLedger.capacityRefusal(error)
 return refusal?`${error.message} [limits=${[...new Set(refusal.limiting.map(endpoint=>endpoint.kind))].join(',')}]`:error.message
}
