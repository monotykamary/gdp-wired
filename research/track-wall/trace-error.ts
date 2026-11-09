// Bounded diagnostic text only; never traverse an arbitrary thrown object.
export function traceError(value: unknown): string {
  if (value instanceof Error) return `${value.name}: ${value.message}`.slice(0, 200)
  switch (typeof value) {
    case 'string': return value.slice(0, 200)
    case 'number': return value.toString().slice(0, 200)
    case 'bigint': return value.toString().slice(0, 200)
    case 'boolean': return value ? 'true' : 'false'
    case 'symbol': return value.toString().slice(0, 200)
    case 'undefined': return 'undefined'
    default: return value === null ? 'null' : '<non-Error object>'
  }
}
