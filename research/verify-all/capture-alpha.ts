// A comparison-only projection, never executable machine syntax. Bound names
// become objects, so no free string name can alias the canonical binder marker.
export function alphaProjection(v: any, env = new Map<string, number>(), depth = 0): any {
  if (!v || typeof v !== 'object') return v
  if (Array.isArray(v)) return v.map(y => alphaProjection(y, env, depth))
  const marker = (name: string) => ({bound: env.get(name)})
  if (v.op === 'var' && env.has(v.name)) return {...v, name: marker(v.name)}
  if (typeof v.each === 'string' && v.value !== undefined) {
    const inner = new Map(env); inner.set(v.each, depth)
    return {...v, each: {bound: depth}, value: alphaProjection(v.value, inner, depth + 1)}
  }
  if (typeof v.key === 'string' && v.term !== undefined) {
    const inner = new Map(env); inner.set(v.key, depth)
    return {...v, key: {bound: depth}, term: alphaProjection(v.term, inner, depth + 1)}
  }
  if (v.op === 'all') {
    const names = [v.key, ...(v.keys ?? [])], inner = new Map(env)
    names.forEach((name, i) => inner.set(name, depth + i))
    const bound = (name: string) => ({bound: inner.get(name)})
    return {...v, key: bound(v.key), ...(v.keys ? {keys: v.keys.map(bound)} : {}), c: alphaProjection(v.c, inner, depth + names.length), ...(v.witness ? {witness: alphaProjection(v.witness, env, depth)} : {})}
  }
  return Object.fromEntries(Object.entries(v).map(([k, y]) => [k, alphaProjection(y, env, depth)]))
}
