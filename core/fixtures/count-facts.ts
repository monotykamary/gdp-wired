// Test/audit support only. The archived goals contain countHyp expansions rather
// than declarations. Recover paired scalar/body terms for diagnostics; never use
// this recovery to admit a certificate or manufacture a production declaration.
import {readFileSync, readdirSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {type C, type E, type Machine, type State, evalE, x} from '../machine.ts'
import {type Count, type CountDecl, type Goal, type MapRead, mcGoal, substE} from '../../kernel/kernel.ts'

import {keyValue} from '../../kernel/prove.ts'

export const fixtureDir = `${import.meta.dir}/../../kernel/fixtures/count-facts`
export type FrozenCountGoal = {goal?: string, law?: string, hyps: C[], seed?: Record<string, number>}
export type ResidualCountGoal = {law: string, gg: Goal, witness: Record<string, number>, m: Machine, decls: CountDecl[], reads: MapRead[]}
export const fixtureNames = readdirSync(fixtureDir).filter(f => f.endsWith('.json.gz') && !f.startsWith('residual')).sort()
export const loadFrozen = (name: string): FrozenCountGoal => JSON.parse(gunzipSync(readFileSync(`${fixtureDir}/${name}`)).toString()) as FrozenCountGoal
export const loadModel = (name: string): {model: Record<string, number>, eliminated: boolean, mismatches: number, pickViolations: number} =>
  JSON.parse(gunzipSync(readFileSync(`${fixtureDir}/${name}.model.gz`)).toString()) as {model: Record<string, number>, eliminated: boolean, mismatches: number, pickViolations: number}
export const loadResidual = (): ResidualCountGoal => JSON.parse(gunzipSync(readFileSync(`${fixtureDir}/residual-mldr.json.gz`)).toString()) as ResidualCountGoal

// Missing concrete cells are zero, matching the frozen solver's completion.
export function modelValue(w: Record<string, number>): (e: E) => number {
  const maps: State['maps'] = Object.create(null)
  for (const [cell, value] of Object.entries(w)) {
    const at = cell.indexOf('['); if (at < 0) continue
    const key = keyValue(cell, w); if (key === undefined) continue
    const map = cell.slice(0, at); (maps[map] ??= new Map()).set(key, value)
  }
  const state: State = {scalars: {}, maps: new Proxy(maps, {get: (t, k: string) => t[k] ?? new Map<number, number>()})}
  const m: Machine = {name: 'frozen completion', params: [], inputs: [], state: {}, step: {}, maps: new Proxy({}, {get: () => 0})}
  const env = new Proxy(w, {get: (t, k: string) => Object.hasOwn(t, k) ? t[k] : 0})
  return e => evalE(e, env, state, m)
}

export function pickHypsForCounts(cs: Count[], picks: [string, E[]][]): C[] {
  const ds = cs.map((c, i) => ({map: `diagnostic$count$${i}`, j: 'diagnostic$parameter', key: c.key, below: c.below, body: c.body}))
  const rs: MapRead[] = cs.map((c, i) => [c.v, ds[i]!.map, {op: 'const', value: 0}])
  return mcGoal([], ds, {reads: rs, insts: [], picks})!.hyps.slice(rs.length)
}

export function recoverCounts(hyps: C[]): Count[] {
  // One archived later goal has flattened gdpModel cells without their read
  // definitions. It cannot support an honest concrete-sum reconstruction.
  if (JSON.stringify(hyps).includes('"name":"gdpModel')) return []
  const out = new Map<string, Count>()
  const side = (scalar: E, body: E, wit: string, below: E): void => {
    if (scalar.op !== 'add' || body.op !== 'add') return
    let a = scalar.a, b = body.a
    while (a.op === 'add' && b.op === 'add') {
      if (a.a.op !== 'mul' || b.a.op !== 'mul' || a.a.a.op !== 'var' || a.a.k !== b.a.k) return
      const v = a.a.a.name, key = 'fixture$count$key'
      const c: Count = {v, key, below, body: substE(b.a.a, {vars: {[wit]: x(key)}, maps: {}, flags: {}})}
      const prior = out.get(v)
      if (prior && JSON.stringify(prior) !== JSON.stringify(c)) throw new Error(`inconsistent recovered count ${v}: ${JSON.stringify(prior)} / ${JSON.stringify(c)}`)
      out.set(v, c); a = a.b; b = b.b
    }
  }
  for (const h of hyps) {
    if (h.op !== 'or' || h.xs.length !== 2) continue
    const [a, b] = h.xs
    if (a?.op !== '<=' || b?.op !== 'and' || b.xs.length !== 2) continue
    const [range, cmp] = b.xs
    if (range?.op !== '<' || range.a.op !== 'var' || cmp?.op !== '<') continue
    side(a.a, cmp.b, range.a.name, range.b); side(a.b, cmp.a, range.a.name, range.b)
  }
  return [...out.values()]
}
