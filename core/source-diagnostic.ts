// JSON-safe native witnesses. Keep absence and non-finite numbers explicit; never
// invoke a getter while printing an error. This is diagnostic data, not a replay format.
export function sourceDiagnostic(value: unknown, active = new Set<object>(), depth = 0): unknown {
  if (value === undefined) return {$undefined: true}
  if (typeof value === 'number' && !Number.isFinite(value)) return {$number: String(value)}
  if (typeof value === 'bigint') return {$bigint: String(value)}
  if (typeof value === 'function' || typeof value === 'symbol') return {$unsupported: typeof value}
  if (value === null || typeof value !== 'object') return value
  if (active.has(value)) return {$circular: true}
  if (depth >= 32) return {$truncated: true}
  active.add(value)
  const visit = (v: unknown) => sourceDiagnostic(v, active, depth + 1)
  try {
    if (value instanceof Date) return {$date: Number.isNaN(Number(value)) ? 'Invalid Date' : value.toISOString()}
    if (value instanceof Map) return {$map: [...value].map(([k, v]) => [visit(k), visit(v)])}
    if (value instanceof Set) return {$set: [...value].map(visit)}
    if (Array.isArray(value)) return value.map(visit)
    return Object.fromEntries(Object.entries(Object.getOwnPropertyDescriptors(value)).map(([k, d]) => [k, 'value' in d ? visit(d.value) : {$accessor: true}]))
  } finally { active.delete(value) }
}
