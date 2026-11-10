// Research-only algebraic audit, not a kernel proof or a production lemma.
// Freeze only genuine scalar/parameter/request assignments. Never trust the
// solver's independently named flags or count columns as their definitions.
import {type C, type E, type Machine} from '../../core/machine.ts'
export function symbolicStutter(m: Machine, model: Record<string, number>): {unchanged: boolean, flags: Record<string, boolean | undefined>, equations: string[]} {
  const env = new Map([...m.params, ...m.inputs, ...Object.keys(m.state)].filter(k => Number.isSafeInteger(model[k]) && model[k]! >= 0).map(k => [k, model[k]!])), flags: Record<string, boolean | undefined> = {}
  function value(e: E, blocked = new Set<string>()): number | undefined {
    if (e.op === 'const') return e.value
    if (e.op === 'var') return blocked.has(e.name) ? undefined : env.get(e.name)
    if (e.op === 'get' || e.op === 'tup' || e.op === 'proj') return undefined
    if (e.op === 'if') { const c = cond(e.c, blocked); return c === undefined ? undefined : value(c ? e.then : e.else, blocked) }
    const a = value(e.a, blocked)
    if (a === undefined) return undefined
    if (e.op === 'mul') return Number.isSafeInteger(a * e.k) ? a * e.k : undefined
    const b = value(e.b, blocked)
    if (b === undefined) return undefined
    const r = e.op === 'add' ? a + b : e.op === 'sub' ? Math.max(0, a - b) : e.op === 'min' ? Math.min(a, b) : e.op === 'max' ? Math.max(a, b) : a * b
    return Number.isSafeInteger(r) ? r : undefined
  }
  function cond(c: C, blocked = new Set<string>()): boolean | undefined {
    if (c.op === 'flag') return flags[c.name]
    if (c.op === 'all') return undefined
    if (c.op === 'not') { const x = cond(c.x, blocked); return x === undefined ? undefined : !x }
    if (c.op === 'and' || c.op === 'or') {
      const xs = c.xs.map(x => cond(x, blocked))
      if (c.op === 'and') return xs.includes(false) ? false : xs.every(x => x === true) ? true : undefined
      return xs.includes(true) ? true : xs.every(x => x === false) ? false : undefined
    }
    const a = value(c.a, blocked), b = value(c.b, blocked)
    return a === undefined || b === undefined ? undefined : c.op === '<' ? a < b : c.op === '<=' ? a <= b : a === b
  }
  function reduce(e: E, blocked = new Set<string>()): E {
    const n = value(e, blocked)
    if (n !== undefined) return {op: 'const', value: n}
    if (e.op === 'if') { const c = cond(e.c, blocked); return c === undefined ? e : reduce(c ? e.then : e.else, blocked) }
    if (e.op === 'get') return {...e, key: reduce(e.key, blocked)}
    return e
  }
  for (const [name, c] of Object.entries(m.step.flags ?? {})) flags[name] = cond(c)
  const same = (a: E, b: E, blocked = new Set<string>()) => JSON.stringify(reduce(a, blocked)) === JSON.stringify(reduce(b, blocked))
  const equations: string[] = []
  let unchanged = !m.history
  for (const [name, e] of Object.entries(m.step.state ?? {})) {
    const equal = same(e, {op: 'var', name})
    equations.push(`${name}: ${equal ? 'identity' : 'not established'}`); unchanged &&= equal
  }
  for (const [name, update] of Object.entries(m.step.maps ?? {})) {
    const key: E = 'each' in update ? {op: 'var', name: update.each} : update.key, blocked = new Set('each' in update ? [update.each] : [])
    const equal = same(update.value, {op: 'get', map: name, key}, blocked)
    equations.push(`${name}: ${equal ? 'identity' : 'not established'}`); unchanged &&= equal
  }
  return {unchanged, flags, equations}
}
