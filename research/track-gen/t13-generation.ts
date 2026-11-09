// T-13: the production generation path, with no proof queries.
import {gzipSync} from 'node:zlib'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates, guardLaws, cprof} from '../../core/counts.ts'
import {smallOf, trueSmall} from '../../core/exists.ts'
import {counted, clock, fullRate, withWall, queryHook} from '../../kernel/prove.ts'
import type {Law} from '../../core/machine.ts'
export const canonical = (l: Law) => {
  const ns = [l.forall, ...(l.keys ?? [])].filter((n): n is string => !!n), keys = new Map(ns.map((n, i) => [n, `B${i}`]))
  const walk = (v: unknown): unknown => Array.isArray(v) ? v.map(walk) : v && typeof v === 'object' ? Object.fromEntries(Object.entries(v).map(([k, x]) => [k, k === 'name' && typeof x === 'string' ? keys.get(x) ?? x : walk(x)])) : v
  return JSON.stringify(walk(l.holds))
}
if (import.meta.main) {
  const only = process.argv[2], records = []
  let queries = 0; queryHook.on = () => { queries++ }
  for (const p of protocols.filter(p => !only || p.id === only)) {
    const t0 = performance.now(), phases: Record<string, number> = {}
    const time = <T>(key: string, f: () => T): T => { const t = performance.now(); try { return f() } finally { phases[key] = performance.now() - t } }
    const r = p.make(), caller = [...r.kindLaws(), ...p.laws(r)]
    const g = time('guards', () => guardLaws(r.machine)), m = {...r.machine, counts: {...r.machine.counts, ...g.counts}}
    const states = time('small', () => smallOf(m, process.env.T13_FRESH_SAMPLES === '1' ? undefined : r.machine))
    const laws = withWall(performance.now() + 60000, () => counted(fullRate, () => {
      // Raw existential callers are not ordinary state laws; their witness
      // selection is a separate production path, not a generation query.
      if (!caller.filter(l => !l.some?.length).every(l => trueSmall(m, [l]))) throw Error(`${p.id}: caller fails samples`)
      return [...caller, ...time('candidates', () => candidates(r.machine, m, caller, caller, g.laws, 60000, clock() + 60000))]
    }, true))
    const record = {id: p.id, count: laws.length, canonical: laws.map(canonical), names: laws.map(l => l.name), wallMs: performance.now() - t0, phases, states: states.map(s => s.sts.length), counts: Object.keys(m.counts), cprof: {...cprof}}
    records.push(record)
    console.error(JSON.stringify({...record, canonical: undefined, names: undefined}))
  }
  console.log('T13_DATA_GZIP_BASE64 ' + gzipSync(JSON.stringify({queries, records})).toString('base64'))
  if (queries) throw Error('generation ran a proof query')
}
