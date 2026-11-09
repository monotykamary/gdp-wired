// Bounded diagnostic text only; never traverse an arbitrary thrown object.
export function traceError(value: unknown): string {
  const text = value instanceof Error ? `${value.name}: ${value.message}`
    : value === null ? 'null'
      : typeof value === 'object' || typeof value === 'function' ? '<non-Error object>'
        : String(value)
  return text.slice(0, 200)
}
