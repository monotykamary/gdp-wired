// Search-only hash consing. A reader's identity-keyed values and dependency edges
// should be shared by structurally identical terms, even after substitution made
// separate objects. No algebraic rewriting, reordering, or kernel acceptance here.
// The returned function is local to a reader; its AST inputs must remain immutable.
export function shareTerms(): <T extends object>(term: T) => T {
  const memo = new WeakMap<object, object>(), ids = new WeakMap<object, number>(), table = new Map<string, object>()
  let next = 0
  const share = <T extends object>(term: T): T => {
    const had = memo.get(term)
    if (had) return had as T
    const entries = Object.entries(term).map(([k, value]) => [k, value !== null && typeof value === 'object' ? share(value as object) : value] as const)
    const key = JSON.stringify([Array.isArray(term) ? ['array', term.length] : ['object'], entries.map(([k, value]) => [k,
      value !== null && typeof value === 'object' ? ['ref', ids.get(value)] : [typeof value, typeof value === 'number' && Object.is(value, -0) ? '-0' : String(value)]
    ]).sort(([a], [b]) => String(a).localeCompare(String(b)))])
    let out = table.get(key)
    if (!out) {
      out = entries.every(([k, value]) => (term as Record<string, unknown>)[k] === value) ? term : Object.assign(Array.isArray(term) ? new Array(term.length) : {}, Object.fromEntries(entries)) as object
      table.set(key, out); ids.set(out, next++)
    }
    memo.set(term, out)
    memo.set(out, out)
    return out as T
  }
  return share
}
