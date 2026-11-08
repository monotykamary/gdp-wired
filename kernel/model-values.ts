// Untrusted MBQI proposals for naturals that are values, not map keys.
// A model supplies the other terms in a linear comparison. Its boundary and
// neighbours are candidate constants; only the instantiated law is assumed,
// and the ordinary kernel must still check the resulting proof.
import {type C, type E, walkOnce} from '../core/machine.ts'

export function modelValueTerms(body: C, name: string, free: ReadonlySet<string>, value: (e: E) => number | undefined): E[] {
  // Function arguments are keys too. Preserve their existing symbolic domain:
  // replacing f(k)'s key by an equal-valued constant can lose later instances.
  // Only a natural never used as a read key gets arithmetic boundary proposals.
  let keyed = false
  walkOnce(body, o => {
    const e = o as E
    if (e.op !== 'get') return
    walkOnce(e.key, k => { const part = k as E; if (part.op === 'var' && part.name === name) keyed = true })
  })
  if (keyed) return []
  type Linear = {coefficient: number, constant: number}
  const linear = (e: E): Linear | undefined => {
    if (e.op === 'var' && e.name === name) return {coefficient: 1, constant: 0}
    if (e.op === 'add') {
      const a = linear(e.a), b = linear(e.b)
      return a && b ? {coefficient: a.coefficient + b.coefficient, constant: a.constant + b.constant} : undefined
    }
    if (e.op === 'mul') {
      const a = linear(e.a)
      return a ? {coefficient: e.k * a.coefficient, constant: e.k * a.constant} : undefined
    }
    const text = JSON.stringify(e)
    if ([...free].some(n => text.includes(`"name":${JSON.stringify(n)}`))) return undefined
    const constant = value(e)
    return constant === undefined || !Number.isSafeInteger(constant) ? undefined : {coefficient: 0, constant}
  }
  const terms = new Set<number>()
  const visit = (c: C): void => {
    if (c.op === 'not') return visit(c.x)
    if (c.op === 'and' || c.op === 'or') { c.xs.forEach(visit); return }
    if (c.op !== '=' && c.op !== '<=' && c.op !== '<') return
    const a = linear(c.a), b = linear(c.b)
    if (!a || !b) return
    const coefficient = a.coefficient - b.coefficient, constant = b.constant - a.constant
    if (!coefficient || !Number.isSafeInteger(coefficient) || !Number.isSafeInteger(constant)) return
    const boundary = Math.floor(constant / coefficient)
    for (const v of [boundary, boundary + 1, boundary - 1]) if (Number.isSafeInteger(v) && v >= 0) terms.add(v)
  }
  visit(body)
  return [...terms].slice(0, 16).map(value => ({op: 'const', value}))
}
