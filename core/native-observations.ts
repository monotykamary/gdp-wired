// Occurrence-bound observations from native harness execution, never model
// inputs. These records describe one actual callback; absent reads stay absent.
export type NativeCallObservation = {kind: 'returned', value: unknown} | {kind: 'raised', raised: string}
export type NativeExecutionObservation = {
  invocation: number,
  calls: Record<string, NativeCallObservation>,
  clock?: number,
}
export type NativeReading = {code: string, key: string, kind: 'answer' | 'raises' | 'clock', method?: string}
const record = (value: unknown): value is Record<string, unknown> =>
  value !== null && typeof value === 'object' && !Array.isArray(value) &&
  (Object.getPrototypeOf(value) === null || Object.getPrototypeOf(value) === Object.prototype)
export function validateNativeObservations(value: unknown, allowedCalls: ReadonlySet<string>): NativeExecutionObservation {
  if (!record(value) || !Number.isSafeInteger(value.invocation) || (value.invocation as number) <= 0 || !record(value.calls))
    throw new Error('native observation invocation/calls unavailable')
  if (value.error !== undefined && value.error !== null) throw new Error(`native observation unavailable: ${typeof value.error === 'string' ? value.error : 'invalid non-string error payload'}`)
  if (value.clock !== undefined && (typeof value.clock !== 'number' || !Number.isSafeInteger(value.clock)))
    throw new Error('native observed clock is outside the exact integer range')
  for (const [key, call] of Object.entries(value.calls)) {
    if (!allowedCalls.has(key)) throw new Error(`native observation of unbound call ${key}`)
    if (!record(call)) throw new Error(`native observation of ${key} is not a record`)
    if (call.kind === 'returned') {
      if (!Object.hasOwn(call, 'value') || Object.hasOwn(call, 'raised')) throw new Error(`ambiguous native return of ${key}`)
      if (typeof call.value === 'number' && !Number.isSafeInteger(call.value)) throw new Error(`native return of ${key} is outside the exact integer range`)
    } else if (call.kind === 'raised') {
      if (typeof call.raised !== 'string' || !call.raised || Object.hasOwn(call, 'value')) throw new Error(`ambiguous native exception of ${key}`)
    } else throw new Error(`native observation of ${key} has no outcome`)
  }
  return value as NativeExecutionObservation
}
// One reader per native harness. Repeated access to a current response is
// cached by its adapter; a later response must never reuse an old invocation.
export function nativeObservationSequence(allowedCalls: ReadonlySet<string>): (value: unknown) => NativeExecutionObservation {
  let previous = 0
  return value => {
    const observed = validateNativeObservations(value, allowedCalls)
    if (observed.invocation <= previous) throw new Error('native execution observation is stale or repeated')
    previous = observed.invocation
    return observed
  }
}
