// Bounded diagnostic text only; never traverse an arbitrary thrown object.
export function traceError(value: unknown): string {
  if (value instanceof Error) return `${value.name}: ${value.message}`.slice(0, 200)
  if (typeof value === 'string') return value.slice(0, 200)
  if (typeof value === 'number') return value.toString().slice(0, 200)
  if (typeof value === 'bigint') return value.toString().slice(0, 200)
  if (typeof value === 'boolean') return value ? 'true' : 'false'
  if (typeof value === 'symbol') return value.toString().slice(0, 200)
  if (value === undefined) return 'undefined'
  return value === null ? 'null' : '<non-Error object>'
}
